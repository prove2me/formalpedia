-- Prove2me | solution 1 for QuadraticFloor.one_apply_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:41.529478+00:00
-- url     : https://prove2.me/submissions/d5698517-d36c-4cc7-86ba-00a4ff13b48f

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_ite_of_neg
public import Theorems.Thm_QuadraticFloor_ite_of_pos


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (x : ℕ) :
    (1 : DirichletCharacter ℂ 5) (x : ZMod 5) = if 5 ∣ x then 0 else 1 := by
  by_cases h5 : 5 ∣ x
  · rw [ite_of_pos h5, MulChar.map_nonunit, ]
    rw [(ZMod.natCast_eq_zero_iff x 5).2 h5]; exact not_isUnit_zero
  · rw [ite_of_neg h5, MulChar.one_apply]
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5)
end QuadraticFloor
