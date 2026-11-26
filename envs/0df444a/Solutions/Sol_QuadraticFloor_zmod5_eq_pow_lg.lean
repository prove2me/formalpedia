-- Prove2me | solution 1 for QuadraticFloor.zmod5_eq_pow_lg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:23.834847+00:00
-- url     : https://prove2.me/submissions/8069bcbe-7d5e-4949-a200-a2e17961fc66

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (a : ZMod 5) (ha : a ≠ 0) : a = 2 ^ lg5 a := by revert a; decide
end QuadraticFloor
