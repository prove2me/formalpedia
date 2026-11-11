-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.physical_error_differential_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:27:27.371402+00:00
-- url     : https://prove2.me/submissions/367b3bb9-72ba-4a04-a059-37eaf42c4d04

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_perturbTop_difference
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualReadout_top
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actual_interval_weight


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
      57 ^ ((n+1)/2 - (a.val+1)/2) *
        HammingWeight ((indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) e) := by
  have h := actual_interval_weight S n sigma (perturbTop S n sigma e) a (TopIndex n)
    (Nat.le_of_lt_succ a.isLt)
  rw [actualReadout_top, actualReadout_top, perturbTop_difference] at h
  exact h
end QEC.Coding.BDL26HistorySyndromeSensitivity
