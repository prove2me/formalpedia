-- Prove2me | solution 1 for QuadraticFloor.starxi_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:21.033267+00:00
-- url     : https://prove2.me/submissions/09150fea-46a4-4457-9231-b4aa73ab0ecf

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
theorem _root_.solution : (star xi) 2 = -Complex.I := by
  rw [MulChar.star_apply, xi_two]; simp
end QuadraticFloor
