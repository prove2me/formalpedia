-- Prove2me | solution 1 for QuadraticFloor.osum_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:30.310125+00:00
-- url     : https://prove2.me/submissions/9a99ca03-aac3-4690-b2a7-187adf3a42f0

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
namespace QuadraticFloor
theorem _root_.solution (t : ℤ) (g h : ℤ → ℤ) : osum t (fun j => g j + h j) = osum t g + osum t h := by
  unfold osum; split_ifs <;> simp [sum_add_distrib] <;> ring
end QuadraticFloor
