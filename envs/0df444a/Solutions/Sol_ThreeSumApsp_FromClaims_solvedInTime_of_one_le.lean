-- Prove2me | solution 1 for ThreeSumApsp.FromClaims.solvedInTime_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:57.013543+00:00
-- url     : https://prove2.me/submissions/1fe756f5-cf3c-41de-9d8a-20307a254025

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Theorems.Thm_ThreeSumApsp_FromClaims_solvedInTimeAt_mono

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
namespace ThreeSumApsp.FromClaims
theorem _root_.solution {Q : EndStatement.Problem}
    (hempty : ∀ x : Q.Instance 0, Q.input x = []) {a : ℝ} {e : ℕ}
    (h : ∀ κ : ℕ, 1 ≤ κ → SolvedInTimeAt Q κ a e) : SolvedInTime Q a e := by
  intro κ
  rcases Nat.eq_zero_or_pos κ with rfl | hκ
  · exact solvedInTimeAt_mono hempty (Nat.zero_le 1) (h 1 le_rfl)
  · exact h κ hκ
end ThreeSumApsp.FromClaims
