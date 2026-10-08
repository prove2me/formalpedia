-- Prove2me | solution 1 for RadGauss.LipschitzGaussian.cubeExtension_spec
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:36:05.916613+00:00
-- url     : https://prove2.me/submissions/04bbabf2-e537-4ff6-8feb-1cc7303c0cd8

import Mathlib
import Definitions.Def_RadGauss_LipschitzGaussian_cubeExtension

namespace B02478c5Aux
open RadGauss.LipschitzGaussian

lemma unit_abs (u : ℤˣ) : |((u : ℤ) : ℝ)| = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

lemma coord_le {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (j : Fin k) : |x j| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x j
  simpa [Real.norm_eq_abs] using this

lemma vertex_apply {k : ℕ} (a : Fin k → ℤˣ) (j : Fin k) :
    (cubeVertex a) j = ((a j : ℤ) : ℝ) := rfl

lemma sep {k : ℕ} (a b : Fin k → ℤˣ) (hab : a ≠ b) :
    2 ≤ ‖cubeVertex a - cubeVertex b‖ := by
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ b j := by
    by_contra h
    push_neg at h
    exact hab (funext h)
  have h1 := coord_le (cubeVertex a - cubeVertex b) j
  rw [PiLp.sub_apply, vertex_apply, vertex_apply] at h1
  have : |((a j : ℤ) : ℝ) - ((b j : ℤ) : ℝ)| = 2 := by
    rcases Int.units_eq_one_or (a j) with h | h <;>
    rcases Int.units_eq_one_or (b j) with h' | h' <;>
    simp_all <;> norm_num
  linarith

lemma uniq {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (a b : Fin k → ℤˣ)
    (ha : ‖x - cubeVertex a‖ < 1) (hb : ‖x - cubeVertex b‖ < 1) : a = b := by
  by_contra hab
  have h2 := sep a b hab
  have : ‖cubeVertex a - cubeVertex b‖ ≤ ‖x - cubeVertex a‖ + ‖x - cubeVertex b‖ := by
    have e : cubeVertex a - cubeVertex b = (x - cubeVertex b) - (x - cubeVertex a) := by abel
    rw [e]
    calc ‖(x - cubeVertex b) - (x - cubeVertex a)‖ ≤ ‖x - cubeVertex b‖ + ‖x - cubeVertex a‖ :=
          norm_sub_le _ _
      _ = _ := by ring
  linarith

lemma eval_near {k : ℕ} (g : (Fin k → ℤˣ) → ℤˣ) (x : EuclideanSpace ℝ (Fin k))
    (a : Fin k → ℤˣ) (ha : ‖x - cubeVertex a‖ < 1) :
    cubeExtension g x = (1 - ‖x - cubeVertex a‖) * ((g a : ℤ) : ℝ) := by
  have h : ∃ a : Fin k → ℤˣ, ‖x - cubeVertex a‖ < 1 := ⟨a, ha⟩
  unfold cubeExtension
  rw [dif_pos h]
  have := uniq x _ _ h.choose_spec ha
  rw [this]

lemma eval_far {k : ℕ} (g : (Fin k → ℤˣ) → ℤˣ) (x : EuclideanSpace ℝ (Fin k))
    (h : ∀ a : Fin k → ℤˣ, 1 ≤ ‖x - cubeVertex a‖) :
    cubeExtension g x = 0 := by
  have h' : ¬ ∃ a : Fin k → ℤˣ, ‖x - cubeVertex a‖ < 1 := by
    rintro ⟨a, ha⟩
    exact absurd (h a) (not_le.mpr ha)
  unfold cubeExtension
  rw [dif_neg h']

lemma tri {k : ℕ} (x y z : EuclideanSpace ℝ (Fin k)) : ‖y - z‖ ≤ ‖x - z‖ + dist x y := by
  have e : y - z = (x - z) - (x - y) := by abel
  rw [e, dist_eq_norm]
  exact norm_sub_le _ _

lemma tri' {k : ℕ} (x y z : EuclideanSpace ℝ (Fin k)) : ‖x - z‖ ≤ ‖y - z‖ + dist x y := by
  have e : x - z = (y - z) + (x - y) := by abel
  rw [e, dist_eq_norm]
  exact norm_add_le _ _

/-- one-sided bound: if `x` is near `a`, then `|f x - f y| ≤ dist x y`. -/
lemma lip_near {k : ℕ} (g : (Fin k → ℤˣ) → ℤˣ) (x y : EuclideanSpace ℝ (Fin k))
    (a : Fin k → ℤˣ) (ha : ‖x - cubeVertex a‖ < 1) :
    |cubeExtension g x - cubeExtension g y| ≤ dist x y := by
  rw [eval_near g x a ha]
  have hga := unit_abs (g a)
  by_cases hy : ∃ b : Fin k → ℤˣ, ‖y - cubeVertex b‖ < 1
  · obtain ⟨b, hb⟩ := hy
    rw [eval_near g y b hb]
    have hgb := unit_abs (g b)
    by_cases hab : a = b
    · subst hab
      rw [← sub_mul, abs_mul, hga, mul_one]
      have h1 := tri x y (cubeVertex a)
      have h2 := tri' x y (cubeVertex a)
      rw [abs_le]; constructor <;> linarith
    · have h2 := sep a b hab
      have h3 : ‖cubeVertex a - cubeVertex b‖ ≤ ‖x - cubeVertex a‖ + dist x y + ‖y - cubeVertex b‖ := by
        have e : cubeVertex a - cubeVertex b =
            (y - cubeVertex b) - (x - cubeVertex a) + (x - y) := by abel
        rw [e, dist_eq_norm]
        calc ‖(y - cubeVertex b) - (x - cubeVertex a) + (x - y)‖
            ≤ ‖(y - cubeVertex b) - (x - cubeVertex a)‖ + ‖x - y‖ := norm_add_le _ _
          _ ≤ (‖y - cubeVertex b‖ + ‖x - cubeVertex a‖) + ‖x - y‖ := by
              gcongr; exact norm_sub_le _ _
          _ = _ := by ring
      have n1 := norm_nonneg (x - cubeVertex a)
      have n2 := norm_nonneg (y - cubeVertex b)
      calc |(1 - ‖x - cubeVertex a‖) * ((g a : ℤ) : ℝ) - (1 - ‖y - cubeVertex b‖) * ((g b : ℤ) : ℝ)|
          ≤ |(1 - ‖x - cubeVertex a‖) * ((g a : ℤ) : ℝ)| + |(1 - ‖y - cubeVertex b‖) * ((g b : ℤ) : ℝ)| :=
            abs_sub _ _
        _ = (1 - ‖x - cubeVertex a‖) + (1 - ‖y - cubeVertex b‖) := by
            rw [abs_mul, abs_mul, hga, hgb, abs_of_pos (by linarith), abs_of_pos (by linarith)]
            ring
        _ ≤ dist x y := by linarith
  · push_neg at hy
    rw [eval_far g y hy, sub_zero, abs_mul, hga, mul_one, abs_of_pos (by linarith)]
    have h1 := hy a
    have h2 := tri x y (cubeVertex a)
    linarith

end B02478c5Aux

open B02478c5Aux in
open RadGauss.LipschitzGaussian in
theorem solution {k : ℕ} (hk : 0 < k) (g : (Fin k → ℤˣ) → ℤˣ) :
    (∀ (x : EuclideanSpace ℝ (Fin k)) (a b : Fin k → ℤˣ),
        ‖x - cubeVertex a‖ < 1 → ‖x - cubeVertex b‖ < 1 → a = b) ∧
      (∀ a, cubeExtension g (cubeVertex a) = ((g a : ℤ) : ℝ)) ∧
      (∀ x, cubeExtension g x ∈ Set.Icc (-1 : ℝ) 1) ∧
      cubeExtension g 0 = 0 ∧
      LipschitzWith 1 (cubeExtension g) := by
  refine ⟨fun x a b ha hb => uniq x a b ha hb, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [eval_near g _ a (by simp)]
    simp
  · intro x
    by_cases hx : ∃ a : Fin k → ℤˣ, ‖x - cubeVertex a‖ < 1
    · obtain ⟨a, ha⟩ := hx
      rw [eval_near g x a ha]
      have hga := unit_abs (g a)
      have n1 := norm_nonneg (x - cubeVertex a)
      have : |(1 - ‖x - cubeVertex a‖) * ((g a : ℤ) : ℝ)| ≤ 1 := by
        rw [abs_mul, hga, mul_one, abs_of_pos (by linarith)]
        linarith
      rw [abs_le] at this
      exact ⟨this.1, this.2⟩
    · push_neg at hx
      rw [eval_far g x hx]
      constructor <;> norm_num
  · apply eval_far
    intro a
    have h := coord_le (0 - cubeVertex a) ⟨0, hk⟩
    rw [PiLp.sub_apply, vertex_apply] at h
    have hu := unit_abs (a ⟨0, hk⟩)
    have h0 : (0 : EuclideanSpace ℝ (Fin k)) ⟨0, hk⟩ = 0 := rfl
    rw [h0, zero_sub, abs_neg, hu] at h
    exact h
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    by_cases hx : ∃ a : Fin k → ℤˣ, ‖x - cubeVertex a‖ < 1
    · obtain ⟨a, ha⟩ := hx
      exact lip_near g x y a ha
    · by_cases hy : ∃ b : Fin k → ℤˣ, ‖y - cubeVertex b‖ < 1
      · obtain ⟨b, hb⟩ := hy
        rw [abs_sub_comm, dist_comm]
        exact lip_near g y x b hb
      · push_neg at hx hy
        rw [eval_far g x hx, eval_far g y hy]
        simp
