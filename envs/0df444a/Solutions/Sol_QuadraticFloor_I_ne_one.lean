-- Prove2me | solution 1 for QuadraticFloor.I_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:06.918637+00:00
-- url     : https://prove2.me/submissions/843e0164-2e75-496b-8535-aaa0c417295f

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution : Complex.I ≠ 1 := by intro h; simpa using congrArg Complex.im h
end QuadraticFloor
