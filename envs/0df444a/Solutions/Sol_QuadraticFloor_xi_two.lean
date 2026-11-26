-- Prove2me | solution 1 for QuadraticFloor.xi_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:47:21.29259+00:00
-- url     : https://prove2.me/submissions/f0aca59a-713a-4f90-ad0f-115fa21568b0

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution : xi 2 = Complex.I := by
  show xiFun 2 = _
  simp only [xiFun, show (2 : ZMod 5) ≠ 0 by decide, ite_false, show lg5 2 = 1 by decide, pow_one]
end QuadraticFloor
