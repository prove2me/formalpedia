-- Prove2me | solution 1 for ProbabilityTheory.convolutionSemigroupOfMeasure_one_coe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:41:26.870682+00:00
-- url     : https://prove2.me/submissions/e0dc18c9-431f-4fde-963f-17610c3c1133

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution
    (μ : MeasureTheory.Measure ℝ) [hμ : MeasureTheory.IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) :
    (((convolutionSemigroupOfMeasure μ h).measure ⟨1, one_pos⟩ :
        MeasureTheory.ProbabilityMeasure ℝ) : MeasureTheory.Measure ℝ) = μ := by
  simp [convolutionSemigroupOfMeasure]
