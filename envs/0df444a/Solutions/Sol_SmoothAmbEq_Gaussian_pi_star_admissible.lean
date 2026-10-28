-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.pi_star_admissible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T20:38:46.06282+00:00
-- url     : https://prove2.me/submissions/7c59a8c1-393c-4599-b255-d5d74f84d528
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate
import Theorems.Thm_SmoothAmbEq_Gaussian_proposition_5_2
import Theorems.Thm_SmoothAmbEq_Gaussian_pi_star_condition_i

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

open SmoothAmbEq.Gaussian

theorem solution (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : max a (1 - 1 / 2 * (M.σ ^ 2 / (M.σ₀ ^ 2 * M.T))) < M.α) (c : Coeffs)
    (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) :
    Admissible M P W (piStar M c) := by
  refine proposition_5_2 M P W hW (piStar M c)
    (pi_star_condition_i M a ha hα c hc P W hW) ?_
  -- the growth bound (5.6): `π*` is linear in `β` with a bounded coefficient
  obtain ⟨hD, h1, h2, h3, -⟩ := hc
  have hσ := M.hσ; have hσ₀ := M.hσ₀; have hk := M.hk
  have hzc : ContinuousOn M.ζ (Icc 0 M.T) := by
    unfold Model.ζ
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    have : 0 ≤ t := ht.1
    positivity
  have hzpos : ∀ t ∈ Icc 0 M.T, M.ζ t ≠ 0 := by
    intro t ht
    unfold Model.ζ
    have : 0 ≤ t := ht.1
    positivity
  have c1 : ContinuousOn c.m₁ (Icc 0 M.T) := fun t ht => (h1 t ht).continuousWithinAt
  have c2 : ContinuousOn c.m₂ (Icc 0 M.T) := fun t ht => (h2 t ht).continuousWithinAt
  have c3 : ContinuousOn c.m₃ (Icc 0 M.T) := fun t ht => (h3 t ht).continuousWithinAt
  have hzi : ContinuousOn (fun t => (M.ζ t)⁻¹) (Icc 0 M.T) := hzc.inv₀ hzpos
  have hA : ContinuousOn (fun t => Real.exp (-M.r * (M.T - t)) / (M.k * M.σ ^ 2)
      * (a₁ M t (c.m₂ t) (c.m₃ t) + M.ζ t * c.m₁ t)) (Icc 0 M.T) := by
    unfold a₁
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.add
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht; exact (hD t ht).ne'
    · fun_prop
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  refine ⟨max B 0 * (1 + |M.r|) + 1, by positivity, fun t ht x β => ?_⟩
  have hBt := hB t ⟨ht.1, ht.2.le⟩
  rw [Real.norm_eq_abs] at hBt
  have hB' : |Real.exp (-M.r * (M.T - t)) / (M.k * M.σ ^ 2)
      * (a₁ M t (c.m₂ t) (c.m₃ t) + M.ζ t * c.m₁ t)| ≤ max B 0 := hBt.trans (le_max_left _ _)
  have hpi : piStar M c t x β = (Real.exp (-M.r * (M.T - t)) / (M.k * M.σ ^ 2)
      * (a₁ M t (c.m₂ t) (c.m₃ t) + M.ζ t * c.m₁ t)) * (β - M.r) := by
    unfold piStar; ring
  rw [hpi, abs_mul]
  have hβr : |β - M.r| ≤ |β| + |M.r| := abs_sub _ _
  have hsq : 0 ≤ Real.sqrt (Real.log (1 + |x|)) := Real.sqrt_nonneg _
  have hM0 : 0 ≤ max B 0 := le_max_right _ _
  calc |Real.exp (-M.r * (M.T - t)) / (M.k * M.σ ^ 2)
        * (a₁ M t (c.m₂ t) (c.m₃ t) + M.ζ t * c.m₁ t)| * |β - M.r|
      ≤ max B 0 * (|β| + |M.r|) := mul_le_mul hB' hβr (abs_nonneg _) hM0
    _ ≤ (max B 0 * (1 + |M.r|) + 1) * (1 + |β| + Real.sqrt (Real.log (1 + |x|))) := by
        have hb : 0 ≤ |β| := abs_nonneg _
        have hr : 0 ≤ |M.r| := abs_nonneg _
        nlinarith [mul_nonneg hM0 hb, mul_nonneg hM0 hr, mul_nonneg (mul_nonneg hM0 hr) hb,
          mul_nonneg (add_nonneg (mul_nonneg hM0 (add_nonneg zero_le_one hr)) zero_le_one) hsq]
