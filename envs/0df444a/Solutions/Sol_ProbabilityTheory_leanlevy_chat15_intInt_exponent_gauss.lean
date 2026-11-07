-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_intInt_exponent_gauss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:06:12.268404+00:00
-- url     : https://prove2.me/submissions/1de4e816-a62a-47d9-9daf-8ee40d60875f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Gaussian component of the smeared Lévy–Khintchine exponent. -/
theorem solution (s ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, ((s : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2)
      = (s : ℂ) * (ξ : ℂ) ^ 2 + (s : ℂ) / 3 := by
  have hquad : ∫ u in (-1 : ℝ)..1, (ξ + u) ^ 2 = 2 * ξ ^ 2 + 2 / 3 := by
    rw [intervalIntegral.integral_comp_add_left (fun v => v ^ 2) ξ, integral_pow]
    ring
  have hc : (fun u : ℝ => ((s : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2))
      = fun u : ℝ => ((s : ℂ) / 2) * (↑((ξ + u) ^ 2 : ℝ) : ℂ) := by
    funext u; push_cast; ring
  rw [hc, show (∫ u in (-1 : ℝ)..1, ((s : ℂ) / 2) * (↑((ξ + u) ^ 2 : ℝ) : ℂ))
        = ((s : ℂ) / 2) * ∫ u in (-1 : ℝ)..1, (↑((ξ + u) ^ 2 : ℝ) : ℂ)
      from intervalIntegral.integral_const_mul _ _,
      intervalIntegral.integral_ofReal, hquad]
  push_cast; ring
