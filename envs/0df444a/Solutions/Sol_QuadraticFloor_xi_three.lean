-- Prove2me | solution 1 for QuadraticFloor.xi_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:29.493296+00:00
-- url     : https://prove2.me/submissions/319126e8-069a-4f98-9cdf-756574d982b8

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution : xi 3 = -Complex.I := by
  show xiFun 3 = _
  simp only [xiFun, show (3 : ZMod 5) ≠ 0 by decide, ite_false, show lg5 3 = 3 by decide]
  rw [pow_three, ← mul_assoc, Complex.I_mul_I]; ring
end QuadraticFloor
