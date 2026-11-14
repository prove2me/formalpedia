-- Prove2me | solution 1 for ProbabilityTheory.IsCompoundPoissonDriver.ae_strictMono_arrival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:33:58.543779+00:00
-- url     : https://prove2.me/submissions/a62646fc-bcd3-42c7-84d4-a85a5dd751a0

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    (h : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, StrictMono (fun n => arrival τ n ω) := by
  filter_upwards [h.ae_interarrival_pos hr] with ω hpos
  refine strictMono_nat_of_lt_succ fun n => ?_
  have hstep : arrival τ (n + 1) ω = arrival τ n ω + τ (n + 1) ω := by
    simp [arrival, Finset.sum_range_succ]
  rw [hstep]
  exact lt_add_of_pos_right _ (hpos (n + 1))
