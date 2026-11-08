-- Prove2me | solution 1 for ProbabilityTheory.convolutionSemigroupOfMeasure_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:47:51.602728+00:00
-- url     : https://prove2.me/submissions/ceb9ddff-3c86-415a-ad40-b1b674af9181

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_convolutionSemigroupOfMeasure_one_coe

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution
    (μ : MeasureTheory.Measure ℝ) [hμ : MeasureTheory.IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) :
    ((convolutionSemigroupOfMeasure μ h).measure ⟨1, one_pos⟩ :
        MeasureTheory.ProbabilityMeasure ℝ) = ⟨μ, hμ⟩ := by
  apply Subtype.ext
  exact convolutionSemigroupOfMeasure_one_coe μ h
