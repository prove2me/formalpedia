-- Prove2me | solution 1 for QuadraticFloor.three_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:51:34.824956+00:00
-- url     : https://prove2.me/submissions/31800b76-0812-4e5d-ac3e-67d22103fd62

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution : ((3 : ℤ) : ZMod 5) ^ 2 = 2 ^ 2 := by decide
end QuadraticFloor
