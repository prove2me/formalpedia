-- Prove2me | solution 1 for QuadraticFloor.vartheta_xi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:30.166396+00:00
-- url     : https://prove2.me/submissions/4a2257ee-cd51-4ed7-8ce0-07d9215614ec

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_xi_four
public import Theorems.Thm_QuadraticFloor_ite_of_pos


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace QuadraticFloor
theorem _root_.solution : vartheta p xi = Theta p := by
  funext x
  unfold vartheta Theta
  have : xi (-1) = -1 := by rw [show (-1 : ZMod 5) = 4 by decide, xi_four]
  rw [ite_of_pos this]
end QuadraticFloor
