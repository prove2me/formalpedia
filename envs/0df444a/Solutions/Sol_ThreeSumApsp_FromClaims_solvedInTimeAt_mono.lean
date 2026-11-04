-- Prove2me | solution 1 for ThreeSumApsp.FromClaims.solvedInTimeAt_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:21.2784+00:00
-- url     : https://prove2.me/submissions/6f829891-98a7-4516-aecd-8bf125140717

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Theorems.Thm_ThreeSumApsp_Dominated_trans


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
namespace ThreeSumApsp.FromClaims
theorem _root_.solution {Q : EndStatement.Problem} (hempty : ∀ x : Q.Instance 0, Q.input x = [])
    {κ κ' : ℕ} (hκ : κ ≤ κ') {a : ℝ} {e : ℕ} (h : SolvedInTimeAt Q κ' a e) :
    SolvedInTimeAt Q κ a e := by
  obtain ⟨P, b, C, hS⟩ := h
  refine ⟨P, b, C, fun n x hx W hW => hS n x (fun a ha => ?_) W hW⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hempty x] at ha
    cases ha
  · exact (hx a ha).trans (Nat.pow_le_pow_right hn hκ)
end ThreeSumApsp.FromClaims
