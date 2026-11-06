-- Prove2me | solution 1 for ProbabilityTheory.cnd_integral_levyCompensatedIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:16:22.321805+00:00
-- url     : https://prove2.me/submissions/cd6f8591-2097-4582-a37a-94b6706c8810

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_cnd_levyCompensatedIntegrand_fixed
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Mathlib.Analysis.RCLike.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    IsConditionallyNegativeDefinite (fun ξ => ∫ x, levyCompensatedIntegrand ξ x ∂ν) := by
  intro n ξ c hc
  have hint : ∀ i j : Fin n,
      Integrable (fun x => starRingEnd ℂ (c i) * c j *
        levyCompensatedIntegrand (ξ i - ξ j) x) ν :=
    fun i j => (integrable_levyCompensatedIntegrand hν _).const_mul _
  have hG_int : Integrable (fun x => ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      levyCompensatedIntegrand (ξ i - ξ j) x) ν :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hint i j
  have key : (∫ x, ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      levyCompensatedIntegrand (ξ i - ξ j) x ∂ν) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        ∫ x, levyCompensatedIntegrand (ξ i - ξ j) x ∂ν := by
    rw [integral_finsetSum Finset.univ
      fun i _ => integrable_finsetSum Finset.univ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_const_mul _ _
  show 0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
    ∫ x, levyCompensatedIntegrand (ξ i - ξ j) x ∂ν).re
  rw [← key, show (∫ x, ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      levyCompensatedIntegrand (ξ i - ξ j) x ∂ν).re =
      ∫ x, (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        levyCompensatedIntegrand (ξ i - ξ j) x).re ∂ν from
    ((@RCLike.reCLM ℂ _).integral_comp_comm hG_int).symm]
  refine integral_nonneg fun x => ?_
  exact cnd_levyCompensatedIntegrand_fixed x n ξ c hc
