-- Prove2me | solution 1 for QuadraticFloor.xi_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:38.942275+00:00
-- url     : https://prove2.me/submissions/a7f175f0-c643-42f9-8c93-1980c3c4958d

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution : xi 0 = 0 := MulChar.map_nonunit _ not_isUnit_zero
end QuadraticFloor
