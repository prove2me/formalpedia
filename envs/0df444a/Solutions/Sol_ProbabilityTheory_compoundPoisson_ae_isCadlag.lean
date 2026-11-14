-- Prove2me | solution 1 for ProbabilityTheory.compoundPoisson_ae_isCadlag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:37:14.729412+00:00
-- url     : https://prove2.me/submissions/95b15454-8fcf-499e-b756-f1800c08e343

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
import Theorems.Thm_ProbabilityTheory_isCadlag_piecewisePath

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {b : ℝ} {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, IsCadlag (fun t => compoundPoisson b τ Y t ω) := by
  filter_upwards [hd.ae_strictMono_arrival hr, hd.ae_tendsto_arrival hr] with ω hmono htop
  exact isCadlag_piecewisePath hmono htop
