-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.xSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:46:15.450951+00:00
-- url     : https://prove2.me/submissions/7c4b4001-0fb2-4074-aceb-76ce359a7f24

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_glue
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_lastCount_glue
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_fiber_sum_family

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
theorem _root_.solution (n : ℕ) : xSum (n + 1) = (fSum n).comp U := by
  unfold xSum fSum
  rw [← Polynomial.coe_compRingHom_apply, map_sum]
  rw [← Finset.sum_fiberwise univ ClosedFamily.restrict]
  apply Finset.sum_congr rfl
  intro D _
  rw [Polynomial.coe_compRingHom_apply, mul_comp, C_comp, X_pow_comp]
  rw [fiber_sum_family D _ (fun J => C (q ^ D.1.D.card) * ((C q * X) ^ J.card * 1 ^ ((adm D.1).card - J.card)))]
  · rw [← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow, add_comm]
  · intro J hJ
    show X ^ (D.1.glue J).lastCount * C (q ^ (D.1.glue J).D.card) = _
    rw [lastCount_glue, card_glue, pow_add, map_mul, one_pow, mul_one, mul_pow, ← C_pow]
    ring
end PretorsionImageClosed.LinearQuiver
