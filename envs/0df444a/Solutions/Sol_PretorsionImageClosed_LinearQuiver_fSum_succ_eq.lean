-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.fSum_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:46:36.016205+00:00
-- url     : https://prove2.me/submissions/27117156-5dbc-450a-b62e-e231ef347ca2

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_glue
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_adm_glue
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
theorem _root_.solution (n : ℕ) :
    fSum (n + 1) = ∑ D : ClosedFamily n, C (q ^ D.1.D.card) * theta (adm D.1) := by
  unfold fSum
  rw [← Finset.sum_fiberwise univ ClosedFamily.restrict]
  apply Finset.sum_congr rfl
  intro D _
  rw [theta, Finset.mul_sum]
  apply fiber_sum_family D _ (fun J => C (q ^ D.1.D.card) * thetaTerm (adm D.1) J)
  intro J hJ
  show C (q ^ (D.1.glue J).D.card) * X ^ (adm (D.1.glue J)).card = _
  rw [card_glue, card_adm_glue hJ, thetaTerm, pow_add, map_mul]
  ring
end PretorsionImageClosed.LinearQuiver
