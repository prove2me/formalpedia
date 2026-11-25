-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.card_candRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:49:07.113614+00:00
-- url     : https://prove2.me/submissions/5ee851a8-cb3a-4f81-9059-6fc74eb6d66c

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction

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
theorem _root_.solution (p : CutoffPair n) : (candRows p).card = p.1.1.rowsReaching + 1 := by
  unfold candRows RowCutoff.rowsReaching
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp
end PretorsionImageClosed.LinearQuiver
