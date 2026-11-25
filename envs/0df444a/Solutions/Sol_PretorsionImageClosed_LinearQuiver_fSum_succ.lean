-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.fSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:51:40.130723+00:00
-- url     : https://prove2.me/submissions/37532222-102c-4b10-af0e-b6c67bb459e4

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_fSum_succ_eq
public import Theorems.Thm_PretorsionImageClosed_Statement_IsDelta_sum
public import Theorems.Thm_PretorsionImageClosed_Statement_theta_eq


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
theorem _root_.solution (n : ℕ) :
    ∃ G, IsDelta (fSum n) G ∧ fSum (n + 1) = X * fSum n + C q * X ^ 2 * G := by
  refine ⟨∑ D : ClosedFamily n, C (q ^ D.1.D.card) * deltaXPow (adm D.1).card, ?_, ?_⟩
  · unfold fSum
    apply IsDelta.sum
    intro D _
    exact (isDelta_X_pow _).C_mul _
  · rw [fSum_succ_eq]
    unfold fSum
    simp only [theta_eq, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intros
      ring
    · apply Finset.sum_congr rfl
      intros
      ring
end PretorsionImageClosed.LinearQuiver
