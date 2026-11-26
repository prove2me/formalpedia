-- Prove2me | solution 1 for QuadraticFloor.ind_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:38.031829+00:00
-- url     : https://prove2.me/submissions/57f5c455-9c94-4213-a89d-0f71caedc994

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {x d : ℕ} (hx : Odd x) (hd : d % 4 = 1) :
    (if x % 8 = d % 8 then (1 : ℂ) else 0) = (1 / 4) * (1 + (ZMod.χ₄ (x : ZMod 4) : ℂ) +
      (ZMod.χ₈ (d : ZMod 8) : ℂ) * ((ZMod.χ₈ (x : ZMod 8) : ℂ) + (ZMod.χ₈' (x : ZMod 8) : ℂ))) := by
  rw [ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight,
    ZMod.χ₈'_nat_eq_if_mod_eight]
  have hx2 : x % 2 = 1 := Nat.odd_iff.1 hx
  have ex2 : x % 2 = x % 8 % 2 := (Nat.mod_mod_of_dvd x (by norm_num)).symm
  have ex4 : x % 4 = x % 8 % 4 := (Nat.mod_mod_of_dvd x (by norm_num)).symm
  have ed2 : d % 2 = d % 8 % 2 := (Nat.mod_mod_of_dvd d (by norm_num)).symm
  have h8 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  have hd8 : d % 8 = 1 ∨ d % 8 = 5 := by omega
  rw [ex2, ex4, ed2]
  rcases h8 with h | h | h | h <;> rcases hd8 with h' | h' <;> simp [h, h'] <;> norm_num
end QuadraticFloor
