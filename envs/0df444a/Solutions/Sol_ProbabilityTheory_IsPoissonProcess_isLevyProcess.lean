-- Prove2me | solution 1 for ProbabilityTheory.IsPoissonProcess.isLevyProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:03:08.425075+00:00
-- url     : https://prove2.me/submissions/a4cd0d73-d868-4ced-ba39-e932c4c829c3

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Data.Nat.Totient
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_PoissonProcess
import Theorems.Thm_ProbabilityTheory_IsPoissonProcess_hasStationaryIncrements

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Complex Finset ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} {μ : Measure Ω}
    (h : IsPoissonProcess N rate μ)
    (hcadlag : ∀ᵐ ω ∂μ, IsCadlag (fun t => (N t ω : ℤ))) :
    IsLevyProcess (fun t ω => (N t ω : ℤ)) μ where
  start_zero := by
    ext ω
    show (N 0 ω : ℤ) = 0
    rw [show N 0 ω = (fun _ => 0) ω from congr_fun h.start_zero ω]
    simp
  indep_increments := h.indep_increments
  stationary_increments := h.hasStationaryIncrements
  cadlag_ae := hcadlag
