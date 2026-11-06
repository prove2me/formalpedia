-- Prove2me | solution 1 for ProbabilityTheory.IsLevyMeasure.isFiniteMeasure_restrict_largeSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:45:02.387029+00:00
-- url     : https://prove2.me/submissions/22571203-957d-49a6-adf5-66de36342ae4

import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    {ε : ℝ} (hε : 0 < ε) : IsFiniteMeasure (ν.restrict (largeSet ε)) := by
  have hfinite : ν {x : ℝ | ε ≤ |x|} < ⊤ := by
    set c := ENNReal.ofReal (min 1 (ε ^ 2))
    set f := fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))
    have hε2 : 0 < min 1 (ε ^ 2) := lt_min one_pos (sq_pos_of_pos hε)
    have hc_pos : 0 < c := ENNReal.ofReal_pos.mpr hε2
    have hf_meas : Measurable f := by
      apply ENNReal.measurable_ofReal.comp
      exact measurable_const.min (measurable_id'.pow_const 2)
    have hSub : {x : ℝ | ε ≤ |x|} ⊆ {x : ℝ | c ≤ f x} := by
      intro x hx
      simp only [mem_setOf_eq] at hx ⊢
      apply ENNReal.ofReal_le_ofReal
      exact min_le_min le_rfl ((sq_abs x).symm ▸ pow_le_pow_left₀ hε.le hx 2)
    have hMarkov := mul_meas_ge_le_lintegral hf_meas c (μ := ν)
    have hle : c * ν {x | ε ≤ |x|} ≤ ∫⁻ x, f x ∂ν :=
      le_trans (mul_le_mul_right (measure_mono hSub) c) hMarkov
    exact lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top hν.2.ne hle) hc_pos.ne'
  exact isFiniteMeasure_restrict.mpr hfinite.ne
