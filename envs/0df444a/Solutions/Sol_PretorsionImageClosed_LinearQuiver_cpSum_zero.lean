-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.cpSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:51:33.239876+00:00
-- url     : https://prove2.me/submissions/5cbd20d1-04bc-4262-9684-0bb1205f2ebf

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
theorem _root_.solution : cpSum 0 = 1 := by
  unfold cpSum
  rw [Fintype.sum_subsingleton _ cutoffPairZero]
  simp [cpWeight, RowCutoff.rowsReaching, middleCount]
end PretorsionImageClosed.LinearQuiver
