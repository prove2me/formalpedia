-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.cpSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:56:16.137168+00:00
-- url     : https://prove2.me/submissions/9a442fc4-771f-43a6-9f8f-0da61cded7d9

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_candRows
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_fiber_sum
public import Theorems.Thm_PretorsionImageClosed_Statement_psi_eq_geomSum


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
    cpSum (n + 1) = ∑ p : CutoffPair n, C (q ^ middleCount p.1.1 p.1.2) * geomSum (p.1.1.rowsReaching + 1) := by
  unfold cpSum
  rw [← Finset.sum_fiberwise univ CutoffPair.restrict cpWeight]
  apply Finset.sum_congr rfl
  intro p _
  rw [fiber_sum, psi_eq_geomSum, card_candRows]
end PretorsionImageClosed.LinearQuiver
