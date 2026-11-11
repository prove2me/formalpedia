-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_upperRamp_indicator_error_le_annulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:13:54.583043+00:00
-- url     : https://prove2.me/submissions/28185d1b-e4ea-4a82-ae3a-575e3c7ef821

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- The bounded ramp differs from the tail indicator only inside the
annulus where the annulus ramp equals one. -/
theorem solution (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (g : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hg_bnd : ∀ x, |g x| ≤ M) (x : ℝ) :
    |min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * g x -
      Set.indicator (largeSet ρ) g x| ≤
      M * max 0 (1 - ((n + 1 : ℝ) / ρ) *
        max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) := by
  have ha0 : 0 ≤ min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) :=
    le_min zero_le_one (le_max_left _ _)
  have ha1 : min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) ≤ 1 :=
    min_le_left _ _
  have hb0 : 0 ≤ max (0 : ℝ) (1 - ((n + 1 : ℝ) / ρ) *
      max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) := le_max_left _ _
  by_cases hx : ρ ≤ |x|
  · have hcoef : 0 ≤ (n + 1 : ℝ) / ρ := by positivity
    have habove : (1 : ℝ) ≤ (|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) hcoef]
    have hcut : min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) = 1 :=
      min_eq_left (le_trans habove (le_max_right _ _))
    rw [Set.indicator_of_mem (show x ∈ largeSet ρ from hx), hcut,
      one_mul, sub_self, abs_zero]
    exact mul_nonneg hM hb0
  · have hxlt : |x| < ρ := lt_of_not_ge hx
    have hnpos : 0 < (n + 1 : ℝ) := by positivity
    have hcoef : 0 ≤ (n + 1 : ℝ) / ρ := by positivity
    by_cases hx' : |x| ≤ ρ - ρ / (n + 1 : ℝ)
    · have hdiff : |x| - ρ ≤ -(ρ / (n + 1 : ℝ)) := by linarith
      have hprod : (ρ / (n + 1 : ℝ)) * ((n + 1 : ℝ) / ρ) = 1 := by
        field_simp [ne_of_gt hnpos, ne_of_gt hρ] <;> ring
      have hscaled : (|x| - ρ) * ((n + 1 : ℝ) / ρ) ≤ -1 := by
        calc
          _ ≤ -(ρ / (n + 1 : ℝ)) * ((n + 1 : ℝ) / ρ) :=
            mul_le_mul_of_nonneg_right hdiff hcoef
          _ = -1 := by rw [neg_mul, hprod]
      have hnonpos : (|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1 ≤ 0 := by
        linarith
      have hcut : min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) = 0 := by
        rw [max_eq_left hnonpos]
        norm_num
      rw [Set.indicator_of_notMem (show x ∉ largeSet ρ from not_le.mpr hxlt),
        hcut, zero_mul, sub_zero, abs_zero]
      exact mul_nonneg hM hb0
    · have hdist : |(|x| - ρ)| ≤ ρ / (n + 1 : ℝ) := by
        rw [abs_of_nonpos (by linarith : |x| - ρ ≤ 0)]
        linarith
      have hinner : max (0 : ℝ) (|(|x| - ρ)| - ρ / (n + 1 : ℝ)) = 0 :=
        max_eq_left (by linarith)
      have hb : max (0 : ℝ) (1 - ((n + 1 : ℝ) / ρ) *
          max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) = 1 := by
        rw [hinner]
        norm_num
      rw [Set.indicator_of_notMem (show x ∉ largeSet ρ from not_le.mpr hxlt),
        sub_zero, abs_mul, abs_of_nonneg ha0, hb, mul_one]
      calc
        min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * |g x|
            ≤ 1 * M := mul_le_mul ha1 (hg_bnd x) (abs_nonneg _) zero_le_one
        _ = M := one_mul _
