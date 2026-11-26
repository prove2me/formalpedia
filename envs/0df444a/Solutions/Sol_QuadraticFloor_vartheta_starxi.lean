-- Prove2me | solution 1 for QuadraticFloor.vartheta_starxi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:33.159079+00:00
-- url     : https://prove2.me/submissions/e6021593-406f-49d6-9946-5ba39b16f545

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
theorem _root_.solution : vartheta p (star xi) = fun x => starRingEnd ℂ (Theta p x) := by
  funext x
  unfold vartheta Theta
  have : (star xi) (-1) = -1 := by
    rw [MulChar.star_apply, show (-1 : ZMod 5) = 4 by decide, xi_four]; simp
  rw [ite_of_pos this, MulChar.star_apply, map_mul, map_mul, map_intCast, map_intCast,
    starRingEnd_apply]
end QuadraticFloor
