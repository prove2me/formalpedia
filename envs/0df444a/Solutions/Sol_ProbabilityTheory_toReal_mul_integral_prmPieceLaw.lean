-- Prove2me | solution 1 for ProbabilityTheory.toReal_mul_integral_prmPieceLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:01:32.080037+00:00
-- url     : https://prove2.me/submissions/4ec6ebea-577a-489f-8507-a7d3f125c6a6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    {E : Type} [MeasurableSpace E] {m : Measure E} [SigmaFinite m]
    [Nonempty E] {k : ℕ} (g : E → ℝ) :
    (m (prmPiece m k)).toReal * ∫ x, g x ∂(prmPieceLaw m k) =
      ∫ x in prmPiece m k, g x ∂m := by
  by_cases h : m (prmPiece m k) = 0
  · rw [h, ENNReal.toReal_zero, zero_mul,
      show (∫ x in prmPiece m k, g x ∂m) =
        ∫ x, g x ∂(m.restrict (prmPiece m k)) from rfl,
      Measure.restrict_eq_zero.mpr h, integral_zero_measure]
  · rw [← integral_smul_prmPieceLaw h, smul_eq_mul]
