-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.fSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:27:06.888808+00:00
-- url     : https://prove2.me/submissions/e01c8716-9f81-45f7-8626-1b8cc28682f6

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_adm

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
theorem _root_.solution : fSum 0 = X := by
  unfold fSum
  rw [Fintype.sum_subsingleton _ closedFamilyZero, card_adm]
  have : admFin closedFamilyZero.1 = ∅ := Finset.eq_empty_of_isEmpty _
  rw [this]
  simp [closedFamilyZero]
end PretorsionImageClosed.LinearQuiver
