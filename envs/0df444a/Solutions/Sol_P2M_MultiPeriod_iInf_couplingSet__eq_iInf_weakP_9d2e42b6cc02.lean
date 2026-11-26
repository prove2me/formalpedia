-- Prove2me | solution 1 for P2M_MultiPeriod_iInf_couplingSet__eq_iInf_weakP_9d2e42b6cc02
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:08.983666+00:00
-- url     : https://prove2.me/submissions/2b1f5331-df67-4de6-969d-e0f21a30bfac

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_Feas_measure_univ
import Theorems.Thm_P2M_CouplingSet__measure_univ_db95189062ba


set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)]
namespace MultiPeriod
theorem _root_.solution
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀] (ν₀ : Measure (Y 0))
    (f : X 0 × Y 0 → ℝ≥0∞) :
    (⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
        ∫⁻ h₀, f h₀ ∂γ₀)
      = ⨅ (γ : WeakP (X 0 × Y 0)) (_ : γ.toMeasure ∈ CouplingSet₀ μ₀ ν₀),
          ∫⁻ h₀, f h₀ ∂γ.toMeasure := by
  refine le_antisymm (le_iInf₂ fun γ hγ => iInf₂_le γ.toMeasure hγ) ?_
  refine le_iInf₂ fun γm hγm => ?_
  haveI hpm : IsProbabilityMeasure γm := ⟨CouplingSet₀.measure_univ hγm⟩
  exact iInf₂_le
    (show WeakP (X 0 × Y 0) from
      (⟨γm, hpm⟩ : ProbabilityMeasure (X 0 × Y 0))) hγm
end MultiPeriod
