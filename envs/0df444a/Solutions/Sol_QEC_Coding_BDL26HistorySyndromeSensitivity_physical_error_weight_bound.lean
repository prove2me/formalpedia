-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.physical_error_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:38:14.754202+00:00
-- url     : https://prove2.me/submissions/752201e5-3497-4c84-866d-44f06d21b02a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_differential_weight
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_physical_error_differential_bound
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (d : Nat) (i : StepIndex d)
variable (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) (a : LevelIndex n) :
    HammingWeight (actualReadout S n sigma a + actualReadout S n (perturbTop S n sigma e) a) ≤
      4 * 57 ^ ((n+1)/2 - (a.val+1)/2) * HammingWeight e := by
  have ht := physical_error_differential_bound S n sigma e a
  have hd := differential_weight S (n+2) (Fin.last (n+1)) e
  exact (ht.trans (Nat.mul_le_mul_left _ hd)).trans_eq (by ac_rfl)
end QEC.Coding.BDL26HistorySyndromeSensitivity
