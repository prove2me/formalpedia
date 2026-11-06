-- Prove2me | solution 1 for ProbabilityTheory.cnd_neg_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:43:57.317499+00:00
-- url     : https://prove2.me/submissions/4a76588e-98aa-46e9-9109-56a483fe2a85

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

theorem solution :
    IsConditionallyNegativeDefinite (fun ξ => -((ξ : ℂ) ^ 2)) := by
  intro n ξ c hc
  show 0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
    (-((↑(ξ i - ξ j) : ℂ) ^ 2))).re
  set W : ℂ := ∑ j, c j * (↑(ξ j) : ℂ) with hW
  have hconj0 : (∑ i, starRingEnd ℂ (c i)) = 0 := by
    rw [← _root_.map_sum, hc, map_zero]
  have hcW : (∑ i, starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) = starRingEnd ℂ W := by
    rw [hW, _root_.map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Complex.conj_ofReal]
  have A : (∑ i, ∑ j, -(starRingEnd ℂ (c i) * (↑(ξ i) : ℂ) ^ 2) * c j) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, hc, mul_zero]
  have B : (∑ i, ∑ j, 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) * (c j * (↑(ξ j) : ℂ)))
      = 2 * starRingEnd ℂ W * W := by
    have hi : ∀ i, (∑ j, 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) * (c j * (↑(ξ j) : ℂ)))
        = 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) * W := by
      intro i
      rw [hW, Finset.mul_sum]
    simp_rw [hi]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hcW]
  have C : (∑ i, ∑ j, -(starRingEnd ℂ (c i) * (c j * (↑(ξ j) : ℂ) ^ 2))) = 0 := by
    have hi : ∀ i, (∑ j, -(starRingEnd ℂ (c i) * (c j * (↑(ξ j) : ℂ) ^ 2)))
        = starRingEnd ℂ (c i) * (∑ j, -(c j * (↑(ξ j) : ℂ) ^ 2)) := by
      intro i
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hi, ← Finset.sum_mul, hconj0, zero_mul]
  have key : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (-((↑(ξ i - ξ j) : ℂ) ^ 2)))
      = 2 * starRingEnd ℂ W * W := by
    have step : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (-((↑(ξ i - ξ j) : ℂ) ^ 2)))
        = (∑ i, ∑ j, (-(starRingEnd ℂ (c i) * (↑(ξ i) : ℂ) ^ 2) * c j
            + 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) * (c j * (↑(ξ j) : ℂ))
            + -(starRingEnd ℂ (c i) * (c j * (↑(ξ j) : ℂ) ^ 2)))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [step]
    rw [show (∑ i, ∑ j, (-(starRingEnd ℂ (c i) * (↑(ξ i) : ℂ) ^ 2) * c j
          + 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) * (c j * (↑(ξ j) : ℂ))
          + -(starRingEnd ℂ (c i) * (c j * (↑(ξ j) : ℂ) ^ 2))))
        = (∑ i, ∑ j, -(starRingEnd ℂ (c i) * (↑(ξ i) : ℂ) ^ 2) * c j)
          + (∑ i, ∑ j, 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) * (c j * (↑(ξ j) : ℂ)))
          + (∑ i, ∑ j, -(starRingEnd ℂ (c i) * (c j * (↑(ξ j) : ℂ) ^ 2)))
        from by simp_rw [Finset.sum_add_distrib]]
    rw [A, B, C]
    ring
  rw [key]
  have hre : ((2 : ℂ) * starRingEnd ℂ W * W).re = 2 * Complex.normSq W := by
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.mul_re]
  rw [hre]
  have := Complex.normSq_nonneg W
  linarith
