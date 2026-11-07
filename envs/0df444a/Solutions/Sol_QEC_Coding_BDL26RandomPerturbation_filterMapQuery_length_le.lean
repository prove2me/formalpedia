-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.filterMapQuery_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:53.851168+00:00
-- url     : https://prove2.me/submissions/21784183-36ba-4904-8e19-009d89e87850

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_filterMapQuery_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A B : Type*} (q : A → Option B × ℕ) (L : List A) :
    (filterMapQuery q L).1.length ≤ L.length := by
  rw [filterMapQuery_value]
  exact List.length_filterMap_le _ _
end QEC.Coding.BDL26RandomPerturbation
