-- Prove2me | solution 1 for QuadraticFloor.vartheta_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:38.539409+00:00
-- url     : https://prove2.me/submissions/a3bc44b4-771b-4c0c-989a-019ecc703f0a

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_one_apply_nat
public import Theorems.Thm_QuadraticFloor_eta_mul_chi4_sq
public import Theorems.Thm_QuadraticFloor_ite_of_neg


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace QuadraticFloor
theorem _root_.solution : vartheta p (1 : DirichletCharacter ℂ 5) =
    fun x => (eta p x : ℂ) * (if 5 ∣ x then 0 else 1) := by
  funext x
  unfold vartheta
  have h1 : (1 : DirichletCharacter ℂ 5) (-1) ≠ -1 := by
    rw [MulChar.one_apply (IsUnit.neg isUnit_one)]; norm_num
  rw [ite_of_neg h1, eta_mul_chi4_sq, one_apply_nat]
end QuadraticFloor
