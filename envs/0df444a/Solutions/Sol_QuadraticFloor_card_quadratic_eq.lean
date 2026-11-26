-- Prove2me | solution 1 for QuadraticFloor.card_quadratic_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:44:40.390982+00:00
-- url     : https://prove2.me/submissions/c76f089d-8379-4173-9737-da9c04030d08

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A B C : ZMod p} (hA : A ≠ 0) (y : ZMod p) :
    ((univ.filter fun x : ZMod p => A * x ^ 2 + B * x + C = y).card : ℤ) =
      quadraticChar (ZMod p) (B ^ 2 - 4 * A * C + 4 * A * y) + 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have h2A : (2 * A : ZMod p) ≠ 0 := mul_ne_zero h2 hA
  have h4A : (4 * A : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) * A = 2 * (2 * A) by ring]; exact mul_ne_zero h2 h2A
  have key : ∀ x : ZMod p, 4 * A * (A * x ^ 2 + B * x + C) =
      (2 * A * x + B) ^ 2 - (B ^ 2 - 4 * A * C) := fun x => by ring
  have hch : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [← quadraticChar_card_sqrts hch, Set.toFinset_ofPred]
  congr 1
  refine card_nbij' (fun x => 2 * A * x + B) (fun z => (z - B) * (2 * A)⁻¹) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have := key x
    rw [hx] at this
    linear_combination -this
  · intro z hz
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
    have hx : 2 * A * ((z - B) * (2 * A)⁻¹) + B = z := by field_simp; ring
    have := key ((z - B) * (2 * A)⁻¹)
    rw [hx, hz] at this
    exact mul_left_cancel₀ h4A (by linear_combination this)
  · intro x _; simp only; field_simp; ring
  · intro z _; simp only; field_simp; ring
end QuadraticFloor
