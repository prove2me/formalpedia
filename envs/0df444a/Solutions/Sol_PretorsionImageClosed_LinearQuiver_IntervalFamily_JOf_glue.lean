-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.IntervalFamily.JOf_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:32:26.858365+00:00
-- url     : https://prove2.me/submissions/90b312e8-47b9-4237-9f4b-b738ad4a429d

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext


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
namespace IntervalFamily
theorem _root_.solution (D : IntervalFamily n) (J : Finset (Fin (n + 1))) : JOf (D.glue J) = J := by
  ext a
  rw [mem_JOf, mem_glue_last]
end IntervalFamily
end PretorsionImageClosed.LinearQuiver
