-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat14_intInt_exponent_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:15:15.437335+00:00
-- url     : https://prove2.me/submissions/a01df86e-936a-41f6-9c55-1c0887b48efb

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Integral of a translated affine function across a symmetric interval. -/
private lemma chat14_intInt_linear (ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, (ξ + u) = 2 * ξ := by
  rw [intervalIntegral.integral_comp_add_left (fun v => v) ξ, integral_id]
  ring

/-- The linear drift term survives the symmetric average with factor two. -/
theorem solution (b ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, ((b : ℂ) * ↑(ξ + u) * Complex.I)
      = 2 * (b : ℂ) * ↑ξ * Complex.I := by
  have hc : (fun u : ℝ => ((b : ℂ) * ↑(ξ + u) * Complex.I))
      = fun u : ℝ => ((b : ℂ) * Complex.I) * (↑(ξ + u) : ℂ) := by
    funext u; ring
  rw [hc, show (∫ u in (-1 : ℝ)..1, ((b : ℂ) * Complex.I) * (↑(ξ + u) : ℂ))
        = ((b : ℂ) * Complex.I) * ∫ u in (-1 : ℝ)..1, (↑(ξ + u) : ℂ)
      from intervalIntegral.integral_const_mul _ _,
      intervalIntegral.integral_ofReal, chat14_intInt_linear]
  push_cast; ring
