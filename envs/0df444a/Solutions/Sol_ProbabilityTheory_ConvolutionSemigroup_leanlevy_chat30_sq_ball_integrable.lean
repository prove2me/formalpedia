-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat30_sq_ball_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T21:30:14.478583+00:00
-- url     : https://prove2.me/submissions/d36c1325-6203-473f-8559-d4bf3b9ef4e3

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Analysis.Normed.Group.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

open ProbabilityTheory.ConvolutionSemigroup

/-- The squared jump size is integrable on any radius ball for a Lévy measure. -/
theorem solution
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (r : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < r} ν := by
  set K : ℝ := max 1 (r ^ 2) with hK_def
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hK_nn : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  refine ⟨(continuous_pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hbound : ∫⁻ x in {x : ℝ | |x| < r}, ‖x ^ 2‖ₑ ∂ν ≤
      ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
    calc ∫⁻ x in {x : ℝ | |x| < r}, ‖x ^ 2‖ₑ ∂ν
        ≤ ∫⁻ x in {x : ℝ | |x| < r}, ENNReal.ofReal (K * min 1 (x ^ 2)) ∂ν := by
          refine setLIntegral_mono ?_ (fun x hx => ?_)
          · exact ENNReal.measurable_ofReal.comp
              (measurable_const.mul (measurable_const.min (measurable_id'.pow_const 2)))
          · rw [Real.enorm_eq_ofReal (sq_nonneg x)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hxr : |x| < r := hx
            by_cases hle : x ^ 2 ≤ 1
            · rw [min_eq_right hle]
              exact le_mul_of_one_le_left (sq_nonneg x) hK1
            · rw [min_eq_left (not_le.mp hle).le, mul_one]
              have hx2 : x ^ 2 < r ^ 2 := by
                have h := abs_lt.mp hxr
                nlinarith [h.1, h.2]
              exact le_trans (le_of_lt hx2) (le_max_right _ _)
      _ = ∫⁻ x in {x : ℝ | |x| < r}, ENNReal.ofReal K * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
          refine lintegral_congr (fun x => ?_)
          rw [ENNReal.ofReal_mul hK_nn]
      _ ≤ ∫⁻ x, ENNReal.ofReal K * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν.2)

