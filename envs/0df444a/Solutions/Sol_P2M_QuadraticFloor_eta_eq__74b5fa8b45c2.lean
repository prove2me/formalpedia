-- Prove2me | solution 1 for P2M_QuadraticFloor_eta_eq__74b5fa8b45c2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:15.127122+00:00
-- url     : https://prove2.me/submissions/bb63f58b-538d-4739-92dd-74a398510ba4

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
public import Theorems.Thm_QuadraticFloor_odd_of_ne_two


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (x : ℕ) : eta p x = kap p x * legendreSym p x := by
  have hpodd := odd_of_ne_two hp2
  unfold eta
  by_cases hx : Even x
  · simp only [hx, ite_true]
    have : kap p (x : ZMod 8) = 0 := by
      unfold kap
      have : x % 2 = 0 := Nat.even_iff.1 hx
      split_ifs
      · rw [ZMod.χ₈'_nat_eq_if_mod_eight]; simp [this]
      · rw [ZMod.χ₈_nat_eq_if_mod_eight]; simp [this]
    rw [this, zero_mul]
  simp only [hx, ite_false]
  have hxodd : Odd x := Nat.not_even_iff_odd.1 hx
  have hsplit : (-8 * p : ℤ) = (-1) * 2 * 2 * 2 * (p : ℤ) := by ring
  rw [hsplit, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left,
    jacobiSym.at_neg_one hxodd, jacobiSym.at_two hxodd,
    jacobiSym.quadratic_reciprocity hpodd hxodd, ← jacobiSym.legendreSym.to_jacobiSym]
  have hx2 : x % 2 = 1 := Nat.odd_iff.1 hxodd
  have hp2' : p % 2 = 1 := Nat.odd_iff.1 hpodd
  -- parity of `(p/2)(x/2)`
  have hsign : ((-1 : ℤ) ^ (p / 2 * (x / 2))) =
      if p % 4 = 1 then 1 else (if x % 4 = 1 then 1 else -1) := by
    split_ifs with h1 h2
    · apply Even.neg_one_pow
      apply Even.mul_right
      rw [Nat.even_div]; omega
    · apply Even.neg_one_pow
      apply Even.mul_left
      rw [Nat.even_div]; omega
    · apply Odd.neg_one_pow
      apply Nat.odd_mul.2
      constructor <;> rw [← Nat.not_even_iff_odd, Nat.even_div] <;> omega
  rw [hsign]
  unfold kap
  rw [ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₈_nat_eq_if_mod_eight]
  have h8 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  have h4 : x % 4 = x % 8 % 4 := (Nat.mod_mod_of_dvd x (by norm_num)).symm
  split_ifs with hp4 <;>
    simp only [ZMod.χ₈'_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight] <;>
    rcases h8 with h | h | h | h <;> simp [h, hx2] <;> omega
end QuadraticFloor
