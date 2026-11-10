-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.fourTuple2Query_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:05:49.851703+00:00
-- url     : https://prove2.me/submissions/b0ec2ba4-4027-424d-b15a-fddf22ea6c8e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_flatMapQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fourTuple1Query_length
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_flatMap_length_of_const


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} (L : List A) (a b : A) :
    (fourTuple2Query L a b).1.length = L.length^2 := by
  rw [fourTuple2Query,flatMapQuery_value,flatMap_length_of_const L _ L.length
    (fun c _ => fourTuple1Query_length L a b c)]
  ring
end QEC.Coding.BDL26RandomPerturbation
