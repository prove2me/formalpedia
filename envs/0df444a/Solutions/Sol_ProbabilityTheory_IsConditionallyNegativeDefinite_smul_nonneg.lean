-- Prove2me | solution 1 for ProbabilityTheory.IsConditionallyNegativeDefinite.smul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:00:12.136656+00:00
-- url     : https://prove2.me/submissions/c4900fae-92ff-4a64-8da6-6e85a7ecdd90

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

theorem solution {a : ℝ} {ψ : ℝ → ℂ}
    (h : IsConditionallyNegativeDefinite ψ) (ha : 0 ≤ a) :
    IsConditionallyNegativeDefinite (fun ξ => (a : ℂ) * ψ ξ) := by
  intro n ξ c hc
  show 0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ((a : ℂ) * ψ (ξ i - ξ j))).re
  have e : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ((a : ℂ) * ψ (ξ i - ξ j))).re
      = a * (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ (ξ i - ξ j)).re := by
    rw [show (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ((a : ℂ) * ψ (ξ i - ξ j)))
        = (a : ℂ) * ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ (ξ i - ξ j) from ?_,
      Complex.re_ofReal_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact mul_nonneg ha (h n ξ c hc)
