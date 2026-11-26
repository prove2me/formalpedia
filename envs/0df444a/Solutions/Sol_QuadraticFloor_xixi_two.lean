-- Prove2me | solution 1 for QuadraticFloor.xixi_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:19.338625+00:00
-- url     : https://prove2.me/submissions/aca1aee0-d444-46dd-a228-dd62ecb71f87

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_xi_two

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution : (xi * xi) 2 = -1 := by
  rw [MulChar.mul_apply, xi_two, Complex.I_mul_I]
end QuadraticFloor
