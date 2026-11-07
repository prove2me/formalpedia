-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_lintegral_sinc_from_min_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:36:25.87832+00:00
-- url     : https://prove2.me/submissions/3601d28b-13dc-4021-81c1-a953fa3ad561

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Finiteness of the sinc damping mass follows from a finite min-square envelope. -/
theorem solution {ν : Measure ℝ}
    (hfinite : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ⊤)
    (hbound : ∀ x : ℝ, 1 - Real.sinc x ≤ 2 * min 1 (x ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤ := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.min (measurable_id'.pow_const 2))
  calc ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν
      ≤ ∫⁻ x, 2 * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
        refine lintegral_mono fun x => ?_
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
          ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (hbound x)
    _ = 2 * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
        lintegral_const_mul 2 hmeas
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hfinite
