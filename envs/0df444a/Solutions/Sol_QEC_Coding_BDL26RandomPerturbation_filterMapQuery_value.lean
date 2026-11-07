-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.filterMapQuery_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:31.31184+00:00
-- url     : https://prove2.me/submissions/48fb24f4-375c-4076-82d6-ffdd1b572571

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A B : Type*} (q : A → Option B × ℕ) (L : List A) :
    (filterMapQuery q L).1 = L.filterMap (fun a => (q a).1) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases he : (q a).1 <;> simp [filterMapQuery,he,ih]
end QEC.Coding.BDL26RandomPerturbation
