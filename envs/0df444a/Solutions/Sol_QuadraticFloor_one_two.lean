-- Prove2me | solution 1 for QuadraticFloor.one_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:28.82988+00:00
-- url     : https://prove2.me/submissions/7c5b0cdb-03c1-4661-a218-779fe6f97446

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution : (1 : DirichletCharacter ℂ 5) 2 = 1 :=
  MulChar.one_apply (IsUnit.of_mul_eq_one (3 : ZMod 5) (by decide))
end QuadraticFloor
