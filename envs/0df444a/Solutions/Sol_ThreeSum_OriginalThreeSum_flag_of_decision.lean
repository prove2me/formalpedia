-- Prove2me | solution 1 for ThreeSum.OriginalThreeSum.flag_of_decision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:03.968751+00:00
-- url     : https://prove2.me/submissions/5fb8ba77-8619-48d6-bec0-cf6b4c1eb3f8

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
import Theorems.Thm_ThreeSum_OriginalThreeSum_distinct_iff_end
import Theorems.Thm_ThreeSumApsp_flag_of
import Theorems.Thm_ThreeSumApsp_flag_of_not


set_option autoImplicit false
open ThreeSum ThreeSum.OriginalThreeSum
open Light ThreeSumApsp.Spec
namespace ThreeSum.OriginalThreeSum
theorem _root_.solution {n : ℕ} (x : Fin n → ℤ) {r : ℤ}
    (hbool : r=0 ∨ r=1) (hcorrect : r=1 ↔ Coloring.DistinctZeroSum x) :
    r=ThreeSumApsp.flag (ThreeSumApsp.ThreeSum x) := by
  by_cases hx : Coloring.DistinctZeroSum x
  · rw [ThreeSumApsp.flag_of ((distinct_iff_end x).mp hx)]
    exact hcorrect.mpr hx
  · rw [ThreeSumApsp.flag_of_not (fun h => hx ((distinct_iff_end x).mpr h))]
    rcases hbool with h | h
    · exact h
    · exact False.elim (hx (hcorrect.mp h))
end ThreeSum.OriginalThreeSum
