-- Prove2me | solution 1 for QuadraticFloor.osum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:49.695848+00:00
-- url     : https://prove2.me/submissions/2721a8d1-4e2c-4edd-a0e2-39167666dfd0

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (g : ℤ → ℤ) : osum 0 g = 0 := by simp [osum]
end QuadraticFloor
