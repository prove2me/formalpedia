-- Prove2me | solution 1 for ProbabilityTheory.aestronglyMeasurable_levyBandPath_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:24:21.38214+00:00
-- url     : https://prove2.me/submissions/4846500d-3d58-4b1e-8d5d-d157c044973a

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Mathlib.Algebra.Notation.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hAfin : ν A < ⊤) (s t : ℝ) :
    AEStronglyMeasurable[prmEvalSigma K X (volume.prod ν) (Set.Ioc s t ×ˢ Set.univ)]
      (compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin s t).toLp _)) μ := by
  have hzero : ∀ᵐ p ∂((volume : Measure ℝ).prod ν),
      p ∉ Set.Ioc s t ×ˢ (Set.univ : Set ℝ) →
        (memLp_two_bandFun hA hAsub hAfin s t).toLp
          ((Set.Ioc s t ×ˢ A).indicator fun q : ℝ × ℝ => q.2) p = 0 := by
    filter_upwards [MemLp.coeFn_toLp (memLp_two_bandFun hA hAsub hAfin s t)] with p hp hpB
    rw [hp]
    apply Set.indicator_of_notMem
    intro hmem
    exact hpB ⟨hmem.1, Set.mem_univ _⟩
  exact aestronglyMeasurable_compensatedPoissonIntegral_prmEvalSigma hd
    (measurableSet_Ioc.prod MeasurableSet.univ) hzero
