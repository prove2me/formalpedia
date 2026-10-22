-- Prove2me | solution 1 for StoneRegression.NearestNeighbor.proposition_10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:36:20.618068+00:00
-- url     : https://prove2.me/submissions/da1ec042-7551-4a2b-a5be-89fed1d26d95

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_NearestNeighbor_Weights



namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

lemma cs_apply {d : ℕ} (bv : Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    coordScale bv u j = bv j * u j := rfl

lemma cs_sq {d : ℕ} (bv : Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    ‖coordScale bv u‖ ^ 2 = ∑ j, (bv j * u j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cs_apply, Real.norm_eq_abs, sq_abs]

lemma cs_le {d : ℕ} (bv : Fin d → ℝ) (a b : ℝ) (ha : 0 < a) (hbv : ∀ j, a ≤ bv j ∧ bv j ≤ b)
    (u : EuclideanSpace ℝ (Fin d)) : ‖coordScale bv u‖ ≤ b * ‖u‖ := by
  have hsq : ‖coordScale bv u‖ ^ 2 ≤ (b * ‖u‖) ^ 2 := by
    rw [cs_sq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, mul_pow]
    have h1 := hbv j
    have : bv j ^ 2 ≤ b ^ 2 := by nlinarith
    nlinarith [sq_nonneg (u j)]
  by_cases hd : ∃ j : Fin d, True
  · obtain ⟨j, -⟩ := hd
    have hb : 0 ≤ b := by linarith [(hbv j).1, (hbv j).2]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq
  · push_neg at hd
    have : coordScale bv u = 0 := by ext j; exact absurd (hd j) (by simp)
    rw [this, norm_zero]
    have : u = 0 := by ext j; exact absurd (hd j) (by simp)
    simp [this]

lemma cs_ge {d : ℕ} (bv : Fin d → ℝ) (a b : ℝ) (ha : 0 < a) (hbv : ∀ j, a ≤ bv j ∧ bv j ≤ b)
    (u : EuclideanSpace ℝ (Fin d)) : a * ‖u‖ ≤ ‖coordScale bv u‖ := by
  have hsq : (a * ‖u‖) ^ 2 ≤ ‖coordScale bv u‖ ^ 2 := by
    rw [cs_sq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, mul_pow]
    have h1 := hbv j
    have : a ^ 2 ≤ bv j ^ 2 := by nlinarith
    nlinarith [sq_nonneg (u j)]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 hsq

lemma cs_lin {d : ℕ} (bv : Fin d → ℝ) (r : ℝ) (u v : EuclideanSpace ℝ (Fin d)) :
    coordScale bv v - coordScale bv u = (1 - r) • coordScale bv v + coordScale bv (r • v - u) := by
  ext j
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, cs_apply, smul_eq_mul]
  ring

theorem p10_core {d : ℕ} (a b : ℝ) (bv : Fin d → ℝ) (ha : 0 < a) (hbv : ∀ j, a ≤ bv j ∧ bv j ≤ b)
    (V : Set (EuclideanSpace ℝ (Fin d))) (hV : V ∈ ConeFamily d (a / b))
    (u v : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) (hv : v ∈ V) (hu0 : 0 < ‖u‖) (huv : ‖u‖ ≤ ‖v‖) :
    ‖coordScale bv v - coordScale bv u‖ < ‖coordScale bv v‖ := by
  have hu0' : u ≠ 0 := norm_pos_iff.1 hu0
  have hvp : 0 < ‖v‖ := lt_of_lt_of_le hu0 huv
  have hv0' : v ≠ 0 := norm_pos_iff.1 hvp
  obtain ⟨j, -⟩ : ∃ j : Fin d, True := by
    by_contra h
    push_neg at h
    exact hu0' (by ext j; exact absurd (h j) (by simp))
  have hb : 0 < b := by linarith [(hbv j).1, (hbv j).2]
  set s := ‖u‖ with hs
  set t := ‖v‖ with ht
  set r := s / t with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := div_le_one_of_le₀ huv (le_of_lt hvp)
  have hcone := hV u hu v hv hu0' hv0'
  set c := a / b with hc
  have hcb : b * c = a := by rw [hc]; field_simp
  have hcpos : 0 < c := by positivity
  -- ‖r v - u‖ < c s
  have hdiff : ‖r • v - u‖ < c * s := by
    have h2 : ‖r • v - u‖ ^ 2 = r ^ 2 * t ^ 2 - 2 * r * inner ℝ u v + s ^ 2 := by
      rw [@norm_sub_sq_real, norm_smul, real_inner_smul_left, real_inner_comm, Real.norm_eq_abs,
        abs_of_nonneg hr0]
      ring
    have hrt : r * t = s := by rw [hr]; field_simp
    have h3 : ‖r • v - u‖ ^ 2 < (c * s) ^ 2 := by
      rw [h2]
      have : r * ((1 - c ^ 2 / 2) * (s * t)) < r * inner ℝ u v := by
        have hrpos : 0 < r := by positivity
        exact mul_lt_mul_of_pos_left hcone hrpos
      have e1 : r ^ 2 * t ^ 2 = s ^ 2 := by rw [← hrt]; ring
      have e2 : r * ((1 - c ^ 2 / 2) * (s * t)) = (1 - c ^ 2 / 2) * s ^ 2 := by
        rw [show r * ((1 - c ^ 2 / 2) * (s * t)) = (1 - c ^ 2 / 2) * s * (r * t) by ring, hrt]; ring
      nlinarith
    exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).1 h3
  rw [cs_lin bv r u v]
  calc ‖(1 - r) • coordScale bv v + coordScale bv (r • v - u)‖
      ≤ ‖(1 - r) • coordScale bv v‖ + ‖coordScale bv (r • v - u)‖ := norm_add_le _ _
    _ ≤ (1 - r) * ‖coordScale bv v‖ + b * ‖r • v - u‖ := by
        gcongr
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        · exact cs_le bv a b ha hbv _
    _ < (1 - r) * ‖coordScale bv v‖ + b * (c * s) := by gcongr
    _ = (1 - r) * ‖coordScale bv v‖ + r * (a * t) := by
        rw [← mul_assoc, hcb, hr]; field_simp
    _ ≤ (1 - r) * ‖coordScale bv v‖ + r * ‖coordScale bv v‖ := by
        gcongr; exact cs_ge bv a b ha hbv v
    _ = ‖coordScale bv v‖ := by ring

end StoneRegression.NearestNeighbor

open StoneRegression.NearestNeighbor


theorem solution {d : ℕ} (a b : ℝ) (bv : Fin d → ℝ) (ha : 0 < a) (hbv : ∀ j, a ≤ bv j ∧ bv j ≤ b)
    (V : Set (EuclideanSpace ℝ (Fin d))) (hV : V ∈ ConeFamily d (a / b))
    (u v : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) (hv : v ∈ V) (hu0 : 0 < ‖u‖) (huv : ‖u‖ ≤ ‖v‖) :
    ‖coordScale bv v - coordScale bv u‖ < ‖coordScale bv v‖ := by
  exact p10_core a b bv ha hbv V hV u v hu hv hu0 huv
