-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.fourTuple1Query_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:01:18.528765+00:00
-- url     : https://prove2.me/submissions/e1d4db73-25ac-4373-8f1f-8d6581804522

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fourTuple1Query_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} (L : List A) (a b c : A) :
    (fourTuple1Query L a b c).1.length = L.length := by
  rw [fourTuple1Query_value,List.length_map]
end QEC.Coding.BDL26RandomPerturbation
