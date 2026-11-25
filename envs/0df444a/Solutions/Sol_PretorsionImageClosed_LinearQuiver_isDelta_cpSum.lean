-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.isDelta_cpSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:07:21.831071+00:00
-- url     : https://prove2.me/submissions/95d761ac-9cae-4de4-8215-f07f28030590

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_cpSum_succ
public import Theorems.Thm_PretorsionImageClosed_Statement_IsDelta_sum


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
theorem _root_.solution (n : ℕ) : IsDelta (X ^ 2 * cpSum n) (cpSum (n + 1)) := by
  rw [cpSum_succ, cpSum, Finset.mul_sum]
  apply IsDelta.sum
  intro p _
  have : X ^ 2 * cpWeight p = C (q ^ middleCount p.1.1 p.1.2) * X ^ (p.1.1.rowsReaching + 1 + 1) := by
    unfold cpWeight
    ring
  rw [this]
  exact (isDelta_X_pow_succ _).C_mul _
end PretorsionImageClosed.LinearQuiver
