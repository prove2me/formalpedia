-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.xSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:50:01.193272+00:00
-- url     : https://prove2.me/submissions/05d37d71-bc0e-42f8-9218-b0c23a59cb54

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_xSum_succ
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_xSum_zero

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
theorem _root_.solution (n : ℕ) : xSum n = gandhiSecondOf (n + 1) := by
  cases n with
  | zero => exact xSum_zero
  | succ m => exact xSum_succ m
end PretorsionImageClosed.LinearQuiver
