-- Prove2me | solution 1 for P2M_FixedOrderFactor_sum_char_pow_eq_one__fb05deb8e53f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:15.981643+00:00
-- url     : https://prove2.me/submissions/1ca86e00-88b8-4f66-be49-ba1514b15966

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters
public import Theorems.Thm_FixedOrderFactor_mem_dualPowers_iff
public import Theorems.Thm_FixedOrderFactor_card_dualPowers
public import Theorems.Thm_FixedOrderFactor_sum_dualPowers
public import Theorems.Thm_FixedOrderFactor_mem_powers_iff

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]
open Classical
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : r ∣ p - 1) (a b : ZMod p) (hb : b ≠ 0) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1),
        χ a * starRingEnd ℂ (χ b) =
      if ∃ c : ZMod p, c ≠ 0 ∧ a = c ^ r * b then (r : ℂ) else 0 := by
  have hterm : ∀ χ : DirichletCharacter ℂ p, χ a * starRingEnd ℂ (χ b) = χ (a * b⁻¹) := by
    intro χ
    rw [show starRingEnd ℂ (χ b) = star (χ b) from rfl, MulChar.star_apply',
      MulChar.inv_apply', map_mul]
  simp_rw [hterm]
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [zero_mul, MulChar.map_zero, Finset.sum_const_zero]
    rw [ite_eq_right_iff.mpr (fun h => absurd h ?_)]
    rintro ⟨c, hc, h⟩
    exact mul_ne_zero (pow_ne_zero r hc) hb h.symm
  · set u : (ZMod p)ˣ := Units.mk0 (a * b⁻¹) (mul_ne_zero ha (inv_ne_zero hb))
    have hu : (u : ZMod p) = a * b⁻¹ := rfl
    rw [← hu]
    have hsum : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter
        (fun χ => χ ^ r = 1), χ u = ∑ χ : dualPowers p r, (χ : MulChar (ZMod p) ℂ) u :=
      Finset.sum_subtype _ (fun χ => by
        rw [Finset.mem_filter, mem_dualPowers_iff]; simp) (fun χ : MulChar (ZMod p) ℂ => χ u)
    rw [hsum, sum_dualPowers, card_dualPowers p hr]
    congr 1
    rw [mem_powers_iff, hu]
    apply propext
    constructor
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by rw [← h]; field_simp⟩
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by rw [h]; field_simp⟩
end FixedOrderFactor
