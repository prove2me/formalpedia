-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.isGandhiSecond_gandhiSecondOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:07:54.834258+00:00
-- url     : https://prove2.me/submissions/1c3b276d-11c2-4b7d-9954-4fd17a1caf08

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_fSum_succ
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_fSum_zero
public import Theorems.Thm_PretorsionImageClosed_Statement_isDelta_X_mul_comp


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution : IsGandhiSecond gandhiSecondOf := by
  refine ⟨rfl, fun m hm => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  cases m with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · show IsDelta (X * 1) 1
      rw [mul_one, ← geomSum_zero, ← pow_one X]
      exact isDelta_X_pow_succ 0
    · show (fSum 0).comp U = U * 1
      rw [fSum_zero, X_comp, mul_one]
  | succ m =>
    obtain ⟨G, hG, hrec⟩ := fSum_succ m
    refine ⟨(fSum m).comp U + C q * U * G.comp U, isDelta_X_mul_comp hG, ?_⟩
    show (fSum (m + 1)).comp U = U * ((fSum m).comp U + C q * U * G.comp U)
    rw [hrec]
    simp only [add_comp, mul_comp, X_comp, C_comp, pow_comp]
    ring
end PretorsionImageClosed.LinearQuiver
