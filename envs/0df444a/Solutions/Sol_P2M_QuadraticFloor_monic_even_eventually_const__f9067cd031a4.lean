-- Prove2me | solution 1 for P2M_QuadraticFloor_monic_even_eventually_const__f9067cd031a4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:42.865894+00:00
-- url     : https://prove2.me/submissions/65bd074b-4186-42ba-a14c-64aae7814323

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
public import Theorems.Thm_QuadraticFloor_osum_congr
public import Theorems.Thm_P2M_QuadraticFloor_monic_even__b68b70dddb0d
public import Theorems.Thm_QuadraticFloor_ediv_small

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (t b : ℤ) :
    ∃ N : ℕ, ∃ c : ℤ, ∀ p : ℕ, p.Prime → N < p → floorSum 1 (2 * t) b p = c := by
  set b' := b - t ^ 2
  set E' : ℤ → ℤ := fun m => if m ^ 2 + b' < 0 then -1 else 1
  refine ⟨(|b'| + t ^ 2).toNat + 2, E' 0 - 2 * osum t E', ?_⟩
  intro p hpp hN
  have : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by omega
  have hsmall : ∀ m : ℤ, |m| ≤ |t| → (((m ^ 2 + b') / (p : ℤ)).negOnePow : ℤ) = E' m := by
    intro m hm
    have hm2 : m ^ 2 ≤ t ^ 2 := sq_le_sq.2 hm
    have hlt : |m ^ 2 + b'| < (p : ℤ) := by
      have h1 := abs_add_le (m ^ 2) b'
      rw [abs_of_nonneg (sq_nonneg m)] at h1
      have : ((|b'| + t ^ 2).toNat : ℤ) = |b'| + t ^ 2 :=
        Int.toNat_of_nonneg (by positivity)
      have hN' : ((|b'| + t ^ 2).toNat : ℤ) + 2 < p := by exact_mod_cast hN
      linarith
    rw [ediv_small hlt]
    simp only [E']
    split_ifs <;> simp
  rw [monic_even' hp2 t b]
  have h0 := hsmall 0 (abs_nonneg t)
  simp only [zero_pow two_ne_zero, zero_add] at h0
  rw [h0, osum_congr hsmall]
end QuadraticFloor
