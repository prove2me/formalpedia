-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_untilt_sinc_density_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:40:45.562229+00:00
-- url     : https://prove2.me/submissions/9841582e-49ea-4714-8d11-9f6d41b03623

import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

/-- The sinc tilt is invertible when the base measure charges no origin atom. -/
theorem solution {ν : Measure ℝ} (hν0 : ν {(0 : ℝ)} = 0) :
    (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))).withDensity
      (fun x => (ENNReal.ofReal (1 - Real.sinc x))⁻¹) = ν := by
  have hpos {x : ℝ} (hx : x ≠ 0) : 0 < 1 - Real.sinc x := by
    rw [Real.sinc_of_ne_zero hx,
      show (1 : ℝ) - Real.sin x / x =
        (x - Real.sin x) / x from by field_simp, div_pos_iff]
    rcases lt_or_gt_of_ne hx with hneg | hpositive
    · right
      refine ⟨?_, hneg⟩
      have h := Real.sin_lt (neg_pos.mpr hneg)
      rw [Real.sin_neg] at h
      linarith
    · exact Or.inl ⟨by linarith [Real.sin_lt hpositive], hpositive⟩
  have hne0 : ∀ᵐ x ∂ν, x ≠ 0 := by
    rw [ae_iff]
    simpa using hν0
  refine withDensity_inv_same
    (ENNReal.measurable_ofReal.comp (measurable_const.sub Real.measurable_sinc))
    ?_ ?_
  · filter_upwards [hne0] with x hx
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpos hx
  · filter_upwards with x using ENNReal.ofReal_ne_top
