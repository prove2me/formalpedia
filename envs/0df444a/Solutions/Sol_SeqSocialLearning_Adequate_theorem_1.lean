-- Prove2me | solution 1 for SeqSocialLearning.Adequate.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:41:27.330983+00:00
-- url     : https://prove2.me/submissions/e63592a9-64f5-4cc1-8edf-7630bad26814
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals
import Theorems.Thm_SeqSocialLearning_Adequate_sufficiency
import Theorems.Thm_SeqSocialLearning_Adequate_necessity

open MeasureTheory ProbabilityTheory

open SeqSocialLearning.Adequate in
theorem solution {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F) :
    AdequateLearning (A := A) μ F ↔ TotallyUnbounded μ F := by
  refine ⟨fun hAL => ?_, sufficiency μ F hF⟩
  by_contra hTU
  obtain ⟨u, hu, hnot⟩ := necessity (A := A) μ F hF hTU
  exact hnot (hAL u hu)
