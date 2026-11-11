-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.fourTuple3Query_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:02:54.327183+00:00
-- url     : https://prove2.me/submissions/60baaade-cba0-4b81-bfa4-c2b760aa6970

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_flatMapQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fourTuple2Query_length
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_flatMap_length_of_const


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} (L : List A) (a : A) :
    (fourTuple3Query L a).1.length = L.length^3 := by
  rw [fourTuple3Query,flatMapQuery_value,flatMap_length_of_const L _ (L.length^2)
    (fun b _ => fourTuple2Query_length L a b)]
  ring
end QEC.Coding.BDL26RandomPerturbation
