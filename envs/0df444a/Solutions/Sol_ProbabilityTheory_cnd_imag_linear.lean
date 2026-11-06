-- Prove2me | solution 1 for ProbabilityTheory.cnd_imag_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:43:01.438228+00:00
-- url     : https://prove2.me/submissions/d251bbae-03a2-4b16-9252-31e6850549d7

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Probability_Characteristic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem solution (a : ℝ) :
    IsConditionallyNegativeDefinite (fun ξ => (a : ℂ) * ↑ξ * I) := by
  intro n ξ c hc
  show 0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
    ((a : ℂ) * ↑(ξ i - ξ j) * I)).re
  have hconj0 : (∑ i, starRingEnd ℂ (c i)) = 0 := by
    rw [← _root_.map_sum, hc, map_zero]
  have expand : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        ((↑(ξ i) : ℂ) - ↑(ξ j)))
      = (∑ i, starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) * (∑ j, c j)
        - (∑ i, starRingEnd ℂ (c i)) * (∑ j, c j * (↑(ξ j) : ℂ)) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsum0 : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      ((a : ℂ) * ↑(ξ i - ξ j) * I)) = 0 := by
    have factored : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
          ((a : ℂ) * ↑(ξ i - ξ j) * I))
        = (a : ℂ) * I * (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
          ((↑(ξ i) : ℂ) - ↑(ξ j))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [factored, expand, hc, hconj0]
    ring
  rw [hsum0]
  simp
