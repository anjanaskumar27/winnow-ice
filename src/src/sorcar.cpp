// C++ includes
#include <iostream>
#include <string>

// C includes
#include <cassert>
#include <unistd.h>

// Project includes
#include "boogie_io.h"
#include "sorcar.h"


/**
 * Displays usage information.
 *
 * @param out The output stream to write to
 */
void display_usage (std::ostream & out)
{
	
	out << "Usage: sorcar [options] file_stem" << std::endl;
	out << "Options:" << std::endl;
	out << "  -a <algorithm>\tSelects the learning algorithm. Valid options are:" << std::endl;
	out << "\t\t\thorndini, sorcar, sorcar-first, sorcar-greedy" << std::endl;
	out << "\t\t\tsorcar-minimal, winnow, perceptron" << std::endl;
	out << "  -f\t\t\tRuns Horndini in the first round." << std::endl;
	out << "  -t\t\t\tAlternates Horndini and Sorcar between rounds." << std::endl;
	out << "  -r\t\t\tResets the set R in each round." << std::endl;
	// Extra options added for Winnow and Sorcar
	out << "  -w\t\t\tDoes not resets weights to initial in each round, instead reads from weights file." << std::endl;
	out << "  -n\t\t\tProposes false in first round for negative examples." << std::endl;
	out << "  -s\t\t\tChoose Sorcar instead of Horndini for ICE classification." << std::endl;
	out << "  -h\t\t\tChoose horndini instead of Sorcar for ICE calssification." << std::endl;
	out << "  -c\t\t\tPrint out number of corrections." << std::endl;
	out << "  -l\t\t\tOnly LTF." << std::endl;
}


/**
 * Enum for selecting the algorithm chosen by the user.
 */
enum algorithm
{
	
	/// Horndini
	HORNDINI = 0,
	
	/// Sorcar with adding all relevant predicates
	SORCAR,
	
	/// Sorcar with greedily adding the first relevant predicate
	SORCAR_FIRST,
	
	/// Sorcar with selecting relevant predicates set using a greedy hitting set algorithm
	SORCAR_GREEDY,
	
	/// Sorcar with selecting a minimal set of relevant predicates
	SORCAR_MINIMAL,

	/// Winnow algorithm
	WINNOW,

	//// Perceptron algorithm
	PERCEPTRON,
	
};

using namespace horn_verification;
 

 /**
  * Command line interface to Sorcar.
  *
  * @param argc The number of command line arguments
  * @param argv The command line arguments
  *
  * @return Returns an POSIX compliant exit code.
  */
int main(int argc, char * const argv[]) {
	
	//
	// Parse command line options
	//
	
	// Variables to hold command line arguments
	bool reset_R = false;
	bool horndini_first_round = false;
	bool alternate = false;
	algorithm alg = algorithm::SORCAR;

	// Extra variables for winnow algorithm
	// If you want to read from weights file
	bool read_W = false;
	bool first_round_false = false;
	bool sorcar_ice = false;
	bool print_corrections = false;
	// By default LTF is considered by Boogie
	int ltf_json = 1;
	int switch_ltf_threshold = 4;
	
	// Parse
	int opt;
	while ((opt = getopt(argc, argv, "a:frtwnscl:j:")) != -1)
	{
		
		switch(opt)
		{
			
			// Algorithm selection
			case 'a':
			{
				
				std::string arg(optarg);
				
				// Parse algorithm
				if (arg == "horndini")
				{
					alg = algorithm::HORNDINI;
				}
				else if (arg == "sorcar")
				{
					alg = algorithm::SORCAR;
				}
				else if (arg == "sorcar-first")
				{
					alg = algorithm::SORCAR_FIRST;
				}
				else if (arg == "sorcar-greedy")
				{
					alg = algorithm::SORCAR_GREEDY;
				}
				else if (arg == "sorcar-minimal")
				{
					alg = algorithm::SORCAR_MINIMAL;
				}
				else if (arg == "winnow")
				{
					alg = algorithm::WINNOW;
				}
				else if (arg == "perceptron")
				{
					alg = algorithm::PERCEPTRON;
				}
				else
				{
					std::cout << "Unknown algorithm '" << arg << "'" << std::endl;
					display_usage(std::cout);
					return EXIT_FAILURE;
				}
				
				break;
				
			}
			
			// Horndini in first round
			case 'f':
			{
				horndini_first_round = true;
				break;
			}

			// Reset R
			case 'r':
			{
				reset_R = true;
				break;
			}
			
			// Alternate between Horndini and Sorcar
			case 't':
			{
				alternate = true;
				break;
			}
			
			// This option reads from weights file
			case 'w':
			{
				read_W = true;
				break;
			}

			// This option makes winnow propose false in the first round		
			case 'n':
			{
				first_round_false = true;
				break;
			}
			// This option chooses Sorcar for ICE sample labeling			
			case 's':
			{
				sorcar_ice = true;
				break;
			}
			
			// This option prints number of corrections		
			case 'c':
			{
				print_corrections = true;
				break;
			}
			// This option only outputs ltf, or only bool or switches from ltf2bool based on threshold	
			case 'l':
			{
				ltf_json = std::atoi(optarg);
				break;
			}
			// This option determines threshold	for switch from ltf2bool
			case 'j':
			{
				switch_ltf_threshold = std::atoi(optarg);
				break;
			}

			// Error (should not happen)
			default:
			{
				display_usage(std::cout);
				return EXIT_FAILURE;
			}
			
		}
		
	}
	
	// Check if only file stem is given
	if (optind != argc - 1)
	{
		std::cout << "Invalid command line arguments." << std::endl;
		display_usage(std::cout);
		return EXIT_FAILURE;
	}

	// File stem
	auto file_stem = std::string(argv[argc - 1]);


	//
	// Read input from files
	//
	
	// Read attribute meta data
	auto metadata = boogie_io::read_attributes_file(file_stem + ".attributes");
	
	// Read data points
	auto datapoints = boogie_io::read_data_file(file_stem + ".data", metadata);

	// Read horn constraints
	auto horn_constraints = boogie_io::read_horn_file(file_stem + ".horn", datapoints);

	// Read intervals
	auto intervals = boogie_io::read_intervals_file(file_stem + ".intervals");

	// Read status (currently only the round number)
	auto round = boogie_io::read_status_file(file_stem + ".status");

	//std::cout << "\n read all files "<< std::endl;
	
	//
	// Check input
	//
	if (metadata.int_names().size() + metadata.categorical_names().size() == 0)
	{
		throw std::runtime_error("No attributes defined");
	}

	//
	// Horndini, compute X
	//
	auto X = sorcar::horndini(datapoints, horn_constraints, intervals);
	assert (sorcar::is_consistent(X, datapoints, horn_constraints));

	//std::cout << "\n computed X "<< std::endl;
	
	std::ofstream out("log.txt", std::ios_base::app);
	out << "alg=" << alg << "; alternate=" << alternate << "; reset-R=" << reset_R << "; first round=" << horndini_first_round;
	
	
	//
	// Plain Horndini (just output Horndini results)
	//
	if (alg == algorithm::HORNDINI)
	{
		boogie_io::write_JSON_file(metadata, X, file_stem + ".json");
		sorcar::write_R_file(file_stem + ".R", X);
	}

	//
	//	Winnow algorithm 
	//
	else if (alg == algorithm::WINNOW)
	{
		// Initialise winnow objects
		std::vector<winnow> winnow_objs;

		// Get number of pedicates for each winnow obj
		for (unsigned i = 0; i < intervals.size(); ++i)
		{
			winnow_objs.push_back(winnow(intervals[i].second - intervals[i].first + 1));
		}

		// Prepare set R
		std::vector<std::set<unsigned>> R;

		if (sorcar_ice == true)
		{
			if (round == 1)
			{
				R.resize(X.size());
			}
			else
			{
				R = sorcar::read_R_file(file_stem + ".R");
			}
			sorcar::reduce_predicates_all(datapoints, horn_constraints, X, R);
			sorcar::write_R_file(file_stem + ".R", R);
		}

		if (read_W == false)
		{
			winnow::execute_algorithm(winnow_objs, datapoints, sorcar_ice ? R : X, horn_constraints);
		}
		else
		{
			if (round != 1)
			{
				// Read from W file
				winnow::read_weights_file(file_stem + ".W", winnow_objs);
			}
			winnow::execute_algorithm(winnow_objs, datapoints, sorcar_ice ? R : X, horn_constraints);
			// Write W file
			winnow::write_weights_file(file_stem + ".W", winnow_objs);
		}

		// Choose option 1 for LTF formula only
		if (ltf_json == 1)
		{
			winnow::write_ltf_json(winnow_objs, metadata, file_stem + ".json");

		}
		// Choose option 2 for Boolean formula only
		else if (ltf_json == 2)
		{
			winnow::write_ltf2bool_json(winnow_objs, metadata, file_stem + ".json", ((first_round_false == true) && (round == 1)));	
		}
		else
		{
			int num_leaves = winnow::write_ltf2bool_json(winnow_objs, metadata, file_stem + ".json", ((first_round_false == true) && (round == 1)));
			if (num_leaves > switch_ltf_threshold) 
			{
				winnow::write_ltf_json(winnow_objs, metadata, file_stem + ".json");
			}
		}
		
		
		/*
		// If not first round, read weights from file
		if (round != 1)
		{
			//winnow::read_weights_file(file_stem + ".W", winnow_objs);
			winnow::execute_algorithm(winnow_objs, datapoints, X, horn_constraints);		
		}

		if (round == 1)
		{
			winnow::write_ltf2bool_json(winnow_objs, metadata, file_stem + ".json", true);
			//winnow::execute_algorithm(winnow_objs, datapoints, X, horn_constraints);
		}
		
		winnow::write_ltf2bool_json(winnow_objs, metadata, file_stem + ".json", false);
		//winnow::write_ltf_json(winnow_objs, metadata, file_stem + ".json");
		// Write W file
		//winnow::write_weights_file(file_stem + ".W", winnow_objs);
		*/
	}
	//
	//	Perceptron algorithm 
	//
	else if (alg == algorithm::PERCEPTRON)
	{
		// Initialise perceptron objects
		std::vector<perceptron> perceptron_objs;

		// Get number of pedicates for each perceptron obj
		for (unsigned i = 0; i < intervals.size(); ++i)
		{
			perceptron_objs.push_back(perceptron(intervals[i].second - intervals[i].first + 1, 0.0));
		}

		// Sorcar instead of Houdini
		// Prepare set R
		std::vector<std::set<unsigned>> R;
		if (reset_R || round == 1)
		{
			R.resize(X.size());
		}
		else
		{
			R = sorcar::read_R_file(file_stem + ".R");
		}
		//sorcar::reduce_predicates_all(datapoints, horn_constraints, X, R);
		//sorcar::write_R_file(file_stem + ".R", R);
		// If not first round, read weights from file
		if (round != 1)
		{
			perceptron::read_weights_file(file_stem + ".W", perceptron_objs);
			perceptron::execute_algorithm(perceptron_objs, datapoints, X, R);		
		}
		if (round == 1)
		{
			perceptron::execute_algorithm(perceptron_objs, datapoints, X, R);	
		}

		perceptron::write_ltf_json(perceptron_objs, metadata, file_stem + ".json");
		perceptron::write_weights_file(file_stem + ".W", perceptron_objs);
	}
	//
	// Sorcar
	//
	else if (alg == algorithm::SORCAR || alg == algorithm::SORCAR_FIRST || alg == algorithm::SORCAR_GREEDY || alg == algorithm::SORCAR_MINIMAL)
	{

		// Prepare set R
		std::vector<std::set<unsigned>> R;
		if (reset_R || round == 1)
		{
			R.resize(X.size());
		}
		else
		{
			R = sorcar::read_R_file(file_stem + ".R");
		}
		std::cout << "; empty R: " << (reset_R || round == 1);
		
		// Run Sorcar if desired and output results
		if (!(horndini_first_round && round == 1) && !(alternate && round % 2 == 1))
		{
			
			// Run Sorcar adding first relevant predicate
			if (alg == algorithm::SORCAR_FIRST)
			{
				sorcar::reduce_predicates_first(datapoints, horn_constraints, X, R);
				std::cout << "; running first Sorcar";
			}

			// Run Sorcar using greedy algorithm for hitting set
			else if (alg == algorithm::SORCAR_GREEDY)
			{
				sorcar::reduce_predicates_greedy(datapoints, horn_constraints, X, R);
				std::cout << "; running greedy Sorcar";
			}

			// Run Sorcar using minimal selection of relevant predicates
			else if (alg == algorithm::SORCAR_MINIMAL)
			{
				sorcar::reduce_predicates_minimal(datapoints, horn_constraints, X, R);
				std::cout << "; running minimal Sorcar";
			}

			// Run vanilla Sorcar (adding all relevant predicates)
			else
			{
				sorcar::reduce_predicates_all(datapoints, horn_constraints, X, R);
				std::cout << "; running vanilla Sorcar";
			}
			
			
			// Output
			boogie_io::write_JSON_file(metadata, R, file_stem + ".json");
			sorcar::write_R_file(file_stem + ".R", R);
			std::cout << "; writing R file" << std::endl;
			
		}
		
		// Otherwise, just output Horndini results
		else
		{
			boogie_io::write_JSON_file(metadata, X, file_stem + ".json");
			sorcar::write_R_file(file_stem + ".R", X);
			std::cout << "; writing R file" << std::endl;
		}
		
	}

	// Error
	else
	{
		throw std::runtime_error("Unknown algorithm selected");
	}
	
	out.close();
	
}

