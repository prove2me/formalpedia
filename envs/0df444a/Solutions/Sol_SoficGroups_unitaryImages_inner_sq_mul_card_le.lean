-- Prove2me | solution 1 for SoficGroups.unitaryImages_inner_sq_mul_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/45959444-6502-45b4-a544-c34393d753f4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_norm_finset_sum_sq_eq_of_pairwise_inner_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
namespace SoficGroups
theorem _root_.solution
    {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ι → H ≃ₗᵢ[ℂ] H) (a b : H)
    (hb : ∀ i : ι, U i b = b)
    (horth : ∀ ⦃i j : ι⦄, i ≠ j →
      inner ℂ (U i a) (U j a) = 0) :
    (Fintype.card ι : ℝ) * ‖inner ℂ a b‖ ^ 2 ≤
      ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  classical
  have hnorm :
      ‖∑ i : ι, U i a‖ ^ 2 =
        (Fintype.card ι : ℝ) * ‖a‖ ^ 2 := by
    calc
      ‖∑ i : ι, U i a‖ ^ 2 =
          ∑ i : ι, ‖U i a‖ ^ 2 := by
            simpa using
              norm_finset_sum_sq_eq_of_pairwise_inner_zero
                (fun i : ι => U i a) Finset.univ horth
      _ = (Fintype.card ι : ℝ) * ‖a‖ ^ 2 := by simp
  have hterm (i : ι) : inner ℂ (U i a) b = inner ℂ a b := by
    calc
      inner ℂ (U i a) b = inner ℂ (U i a) (U i b) := by rw [hb i]
      _ = inner ℂ a b := (U i).inner_map_map a b
  have hinner :
      inner ℂ (∑ i : ι, U i a) b =
        (Fintype.card ι : ℂ) * inner ℂ a b := by
    rw [sum_inner]
    simp_rw [hterm]
    simp [nsmul_eq_mul]
  have hcs :
      (Fintype.card ι : ℝ) * ‖inner ℂ a b‖ ≤
        ‖∑ i : ι, U i a‖ * ‖b‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (∑ i : ι, U i a) b
    rw [hinner, norm_mul, Complex.norm_natCast] at h
    exact h
  have hsq :
      ((Fintype.card ι : ℝ) * ‖inner ℂ a b‖) ^ 2 ≤
        (‖∑ i : ι, U i a‖ * ‖b‖) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hcs
  rw [mul_pow, mul_pow, hnorm] at hsq
  by_cases hcard : Fintype.card ι = 0
  · simp only [hcard, Nat.cast_zero, zero_mul]
    positivity
  · have hpos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hcard
    apply (mul_le_mul_iff_right₀ hpos).mp
    calc
      (Fintype.card ι : ℝ) *
          ((Fintype.card ι : ℝ) * ‖inner ℂ a b‖ ^ 2) =
        (Fintype.card ι : ℝ) ^ 2 * ‖inner ℂ a b‖ ^ 2 := by ring
      _ ≤ ((Fintype.card ι : ℝ) * ‖a‖ ^ 2) * ‖b‖ ^ 2 := hsq
      _ = (Fintype.card ι : ℝ) * (‖a‖ ^ 2 * ‖b‖ ^ 2) := by ring
end SoficGroups
