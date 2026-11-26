-- Prove2me | solution 1 for QuadraticFloor.xi_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:47:45.98506+00:00
-- url     : https://prove2.me/submissions/7d08ad61-973e-446d-9747-1930456274fa

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution : xi 4 = -1 := by
  show xiFun 4 = _
  simp only [xiFun, show (4 : ZMod 5) ≠ 0 by decide, ite_false, show lg5 4 = 2 by decide, pow_two,
    Complex.I_mul_I]
end QuadraticFloor
