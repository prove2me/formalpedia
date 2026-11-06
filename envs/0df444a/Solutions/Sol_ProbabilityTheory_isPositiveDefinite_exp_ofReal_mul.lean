-- Prove2me | solution 1 for ProbabilityTheory.isPositiveDefinite_exp_ofReal_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:49:53.608877+00:00
-- url     : https://prove2.me/submissions/95ea074a-043f-4f14-ab4b-ef6c46787384

import Definitions.Def_LeanLevy_Fourier_PositiveDefinite
import Definitions.Def_LeanLevy_Probability_Characteristic
import Mathlib.Analysis.Matrix.PosDef

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators

theorem solution (x : ℝ) :
    IsPositiveDefinite (fun ξ : ℝ => Complex.exp ((x : ℂ) * (ξ : ℂ) * I)) := by
  set μ : ProbabilityMeasure ℝ := ⟨Measure.dirac x, inferInstance⟩ with hμ
  have h := IsPositiveDefinite.of_charFun μ
  have hfun : (fun ξ : ℝ => charFun (μ : Measure ℝ) ξ)
      = fun ξ : ℝ => Complex.exp ((x : ℂ) * (ξ : ℂ) * I) := by
    funext ξ
    rw [show (μ : Measure ℝ) = Measure.dirac x from rfl, charFun_apply_real, integral_dirac]
    congr 1
    ring
  rwa [hfun] at h
