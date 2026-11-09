-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat24_intInt_exponent_gauss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:21:58.704889+00:00
-- url     : https://prove2.me/submissions/ca800fbd-b7b0-403f-bbed-b6d61f7441ee

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal Real

private lemma chat24_intInt_quadratic (ξ : ℝ) : ∫ u in (-1 : ℝ)..1, (ξ + u) ^ 2 = 2 * ξ ^ 2 + 2 / 3 := by
  rw [intervalIntegral.integral_comp_add_left (fun v => v ^ 2) ξ, integral_pow]
  ring


theorem solution (s ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, ((s : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2)
      = (s : ℂ) * (ξ : ℂ) ^ 2 + (s : ℂ) / 3 := by
  have hc : (fun u : ℝ => ((s : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2))
      = fun u : ℝ => ((s : ℂ) / 2) * (↑((ξ + u) ^ 2 : ℝ) : ℂ) := by
    funext u; push_cast; ring
  rw [hc, show (∫ u in (-1 : ℝ)..1, ((s : ℂ) / 2) * (↑((ξ + u) ^ 2 : ℝ) : ℂ))
        = ((s : ℂ) / 2) * ∫ u in (-1 : ℝ)..1, (↑((ξ + u) ^ 2 : ℝ) : ℂ)
      from intervalIntegral.integral_const_mul _ _,
      intervalIntegral.integral_ofReal, chat24_intInt_quadratic]
  push_cast; ring

