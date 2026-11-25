-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.IntervalFamily.restrict_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:08:50.64552+00:00
-- url     : https://prove2.me/submissions/1e4a7fc1-e68b-4dcc-a582-7f3beb4f7754

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
theorem _root_.solution (D : IntervalFamily n) (J : Finset (Fin (n + 1))) : (D.glue J).restrict = D := by
  ext p
  rw [mem_restrict, mem_glue_castSucc]
end IntervalFamily
end PretorsionImageClosed.LinearQuiver
