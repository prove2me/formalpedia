-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.xSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:31:55.582373+00:00
-- url     : https://prove2.me/submissions/7879ea00-5c5e-4118-9cac-7179bc10effb

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction

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
theorem _root_.solution : xSum 0 = 1 := by
  unfold xSum
  rw [Fintype.sum_subsingleton _ closedFamilyZero]
  simp [fWeight, closedFamilyZero, IntervalFamily.lastCount]
end PretorsionImageClosed.LinearQuiver
