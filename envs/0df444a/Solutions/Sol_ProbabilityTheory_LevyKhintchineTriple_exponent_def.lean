-- Prove2me | solution 1 for ProbabilityTheory.LevyKhintchineTriple.exponent_def
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:30:38.76366+00:00
-- url     : https://prove2.me/submissions/662ce9da-ce44-4eac-9dfb-8381ea288750

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Complex.Basic
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The Lévy–Khintchine exponent unfolds to its source-defined drift, Gaussian and jump terms. -/
theorem solution :
    ∀ (T : ProbabilityTheory.LevyKhintchineTriple) (ξ : ℝ),
      T.exponent ξ =
        ↑T.drift * ↑ξ * Complex.I - ↑↑T.gaussianVariance * ↑ξ ^ 2 / 2 +
          ∫ (x : ℝ), ProbabilityTheory.levyCompensatedIntegrand ξ x ∂T.levyMeasure := by
  intro T ξ
  rfl
