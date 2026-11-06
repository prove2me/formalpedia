-- Prove2me | solution 1 for ProbabilityTheory.IsConditionallyNegativeDefinite.add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:00:06.819857+00:00
-- url     : https://prove2.me/submissions/4ac0ad39-df0e-4a19-bd83-2f845a85fb06

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

theorem solution {ψ₁ ψ₂ : ℝ → ℂ}
    (h₁ : IsConditionallyNegativeDefinite ψ₁) (h₂ : IsConditionallyNegativeDefinite ψ₂) :
    IsConditionallyNegativeDefinite (fun ξ => ψ₁ ξ + ψ₂ ξ) := by
  intro n ξ c hc
  show 0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
    (ψ₁ (ξ i - ξ j) + ψ₂ (ξ i - ξ j))).re
  have e : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ₁ (ξ i - ξ j) + ψ₂ (ξ i - ξ j))).re
      = (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ₁ (ξ i - ξ j)).re
        + (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ₂ (ξ i - ξ j)).re := by
    rw [← Complex.add_re]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact add_nonneg (h₁ n ξ c hc) (h₂ n ξ c hc)
