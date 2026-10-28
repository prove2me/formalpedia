-- Prove2me | solution 1 for RSInt.strip_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:09:26.7081+00:00
-- url     : https://prove2.me/submissions/2b8c6be8-6ddd-4ee2-b89c-61038662316c

import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib

/-  RS_Strip.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 1:
    contour tools.

    Mathlib-only (no corpus import), so the file can serve the dbn island's M5 layer L6 as well.

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `integrable_exp_quad`, `integrable_of_continuous_of_tail` : integrability of a continuous
        function from a Gaussian-type tail bound `C exp(-a v^2 + b |v|)`.
      * `strip_integral_eq` : Cauchy's theorem on a HORIZONTAL STRIP y1 <= Im z <= y2 with decay at
        both ends: the integrals along the two edges agree.  (Mathlib's rectangle theorem
        `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` plus two limits.)
      * `lineUp c F`, `lineDn c F` : the oriented integrals along the slanted lines through the real
        point `c` with directions `1 + I` (slope +1) and `1 - I` (slope -1).
      * `lineUp_eq_of_strip`, `lineDn_eq_of_strip` : line independence -- the integral along the line
        through `c1` equals the one through `c2` when `F` is continuous on the closed slanted strip,
        holomorphic inside, and tends to 0 at infinity in the strip.

    conjecture1_proved = False.  Contour-integration infrastructure; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Integrability from a Gaussian tail -/







/-! ## 2. Cauchy's theorem on a horizontal strip -/


theorem solution {f : ℂ → ℂ} {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂)
    (hcont : ContinuousOn f {z : ℂ | z.im ∈ Icc y₁ y₂})
    (hdiff : DifferentiableOn ℂ f {z : ℂ | z.im ∈ Ioo y₁ y₂})
    (hint₁ : Integrable (fun x : ℝ => f (x + y₁ * I)))
    (hint₂ : Integrable (fun x : ℝ => f (x + y₂ * I)))
    (hdecay : ∀ ε > 0, ∃ R : ℝ, ∀ x y : ℝ, R ≤ |x| → y ∈ Icc y₁ y₂ → ‖f (x + y * I)‖ ≤ ε) :
    ∫ x : ℝ, f (x + y₁ * I) = ∫ x : ℝ, f (x + y₂ * I) := by
  -- the rectangle identity on [-T, T] x [y1, y2]
  have key : ∀ T : ℝ, 0 ≤ T →
      (∫ x in (-T)..T, f (x + y₁ * I)) - (∫ x in (-T)..T, f (x + y₂ * I)) +
        I • (∫ y in y₁..y₂, f (T + y * I)) - I • (∫ y in y₁..y₂, f (-T + y * I)) = 0 := by
    intro T hT
    have hre1 : ((-T : ℝ) + y₁ * I : ℂ).re = -T := by simp
    have him1 : ((-T : ℝ) + y₁ * I : ℂ).im = y₁ := by simp
    have hre2 : ((T : ℝ) + y₂ * I : ℂ).re = T := by simp
    have him2 : ((T : ℝ) + y₂ * I : ℂ).im = y₂ := by simp
    have H := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f
      ((-T : ℝ) + y₁ * I) ((T : ℝ) + y₂ * I) ?_ ?_
    · rw [hre1, him1, hre2, him2] at H
      simpa using H
    · rw [hre1, him1, hre2, him2]
      refine hcont.mono fun z hz => ?_
      rw [mem_reProdIm] at hz
      simp only [mem_setOf_eq]
      rw [Set.uIcc_of_le hy] at hz
      exact hz.2
    · rw [hre1, him1, hre2, him2]
      refine hdiff.mono fun z hz => ?_
      rw [mem_reProdIm] at hz
      simp only [mem_setOf_eq]
      rw [min_eq_left hy, max_eq_right hy] at hz
      exact hz.2
  -- the vertical sides tend to zero
  have hvert : ∀ s : ℝ, s = 1 ∨ s = -1 →
      Tendsto (fun T : ℝ => ∫ y in y₁..y₂, f (s * T + y * I)) atTop (𝓝 0) := by
    intro s hs
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨R, hR⟩ := hdecay (ε / (2 * (y₂ - y₁ + 1))) (by
      have : 0 < y₂ - y₁ + 1 := by linarith
      positivity)
    rw [eventually_atTop]
    refine ⟨max R 0, fun T hT => ?_⟩
    rw [dist_zero_right]
    have hsT : R ≤ |s * T| := by
      rcases hs with rfl | rfl
      · rw [one_mul, abs_of_nonneg (le_trans (le_max_right _ _) hT)]
        exact le_trans (le_max_left _ _) hT
      · rw [neg_one_mul, abs_neg, abs_of_nonneg (le_trans (le_max_right _ _) hT)]
        exact le_trans (le_max_left _ _) hT
    have hb : ∀ y ∈ Set.uIoc y₁ y₂, ‖f (↑s * ↑T + ↑y * I)‖ ≤ ε / (2 * (y₂ - y₁ + 1)) := by
      intro y hy'
      rw [Set.uIoc_of_le hy] at hy'
      have := hR (s * T) y hsT ⟨le_of_lt hy'.1, hy'.2⟩
      rwa [ofReal_mul] at this
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have hpos : 0 < y₂ - y₁ + 1 := by linarith
    calc ‖∫ y in y₁..y₂, f (↑s * ↑T + ↑y * I)‖
        ≤ ε / (2 * (y₂ - y₁ + 1)) * |y₂ - y₁| := this
      _ < ε := by
        rw [abs_of_nonneg (by linarith)]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  have h1 := intervalIntegral_tendsto_integral hint₁ tendsto_neg_atTop_atBot tendsto_id
  have h2 := intervalIntegral_tendsto_integral hint₂ tendsto_neg_atTop_atBot tendsto_id
  have hv1 := hvert 1 (Or.inl rfl)
  have hvm := hvert (-1) (Or.inr rfl)
  simp only [ofReal_one, one_mul, ofReal_neg, neg_mul] at hv1 hvm
  have hlim := ((h1.sub h2).add (hv1.const_smul I)).sub (hvm.const_smul I)
  simp only [smul_zero, add_zero, sub_zero] at hlim
  have hzero : Tendsto (fun T : ℝ =>
      (∫ x in (-T)..(id T), f (x + y₁ * I)) - (∫ x in (-T)..(id T), f (x + y₂ * I)) +
        I • (∫ y in y₁..y₂, f (T + y * I)) - I • (∫ y in y₁..y₂, f (-T + y * I))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    exact ⟨0, fun T hT => (key T hT).symm⟩
  have := tendsto_nhds_unique hlim hzero
  exact sub_eq_zero.mp this
