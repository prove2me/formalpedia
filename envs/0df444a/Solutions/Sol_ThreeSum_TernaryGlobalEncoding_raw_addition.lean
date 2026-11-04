-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.raw_addition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:10:37.161925+00:00
-- url     : https://prove2.me/submissions/b792de9c-9c9c-4aee-a163-f715a4de04c3

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryGlobalEncoding
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq Ω]
variable (maps : I → Coordinate (Fin L) → ZMod p) (occ : Ω → I)
  (edge : Ω → LocalEdge L α π)
namespace ThreeSum.TernaryGlobalEncoding
theorem _root_.solution (w : Coordinate (Fin L) → ZMod p) (e : LocalEdge L α π) :
    rawSource w false (left e)+rawSource w true (right e) = rawOutput w (output e) := by
  unfold rawSource rawOutput
  have hs : (∑ i, ((w (Sum.inl i)).val : ℤ)*(left e i).val)+
      (∑ i, ((w (Sum.inl i)).val : ℤ)*(right e i).val) =
      ∑ i, ((w (Sum.inl i)).val : ℤ)*(output e i).val := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    have h : ((left e i).val : ℤ)+(right e i).val = (output e i).val := by
      exact_mod_cast (edge_data e).2.2.2 i
    rw [← mul_add,h]
  linarith
end ThreeSum.TernaryGlobalEncoding
