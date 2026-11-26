-- Prove2me | solution 1 for QuadraticFloor.xi_sq_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:08.848094+00:00
-- url     : https://prove2.me/submissions/e75a4fe1-0754-4015-a199-f613d4c8609a

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_xi_two
public import Theorems.Thm_QuadraticFloor_xi_three
public import Theorems.Thm_QuadraticFloor_xi_four
public import Theorems.Thm_QuadraticFloor_xi_zero

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (x : ℕ) : (xi (x : ZMod 5)) ^ 2 = (jacobiSym x 5 : ℂ) := by
  rw [jacobiSym.mod_left, ← ZMod.natCast_mod x 5]
  have : (x : ℤ) % ((5 : ℕ) : ℤ) = ((x % 5 : ℕ) : ℤ) := by push_cast; rfl
  rw [this]
  have h5 : x % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases (x % 5)
  · rw [Nat.cast_zero, xi_zero]; norm_num
  · simp
  · rw [Nat.cast_ofNat, xi_two, Complex.I_sq]; norm_num
  · rw [Nat.cast_ofNat, xi_three, neg_sq, Complex.I_sq]; norm_num
  · rw [Nat.cast_ofNat, xi_four]; norm_num
end QuadraticFloor
