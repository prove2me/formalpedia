-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.centeredSampleRowEitherViolationIndicator_hasSubgaussianMGF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:37:26.429274+00:00
-- url     : https://prove2.me/submissions/d5ddf236-c1ee-46c0-ab6d-ad2767a38bca

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sampleRowEitherViolationIndicator_mem_Icc

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    ProbabilityTheory.HasSubgaussianMGF
      (centeredSampleRowEitherViolationIndicator
        Delta hDelta x outWord inWord a)
      (1 / 4 : NNReal)
      (distribution r Delta hDelta).toMeasure := by
  have h :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
      (μ := (distribution r Delta hDelta).toMeasure)
      (X := sampleRowEitherViolationIndicator x outWord inWord a)
      (a := (0 : Real)) (b := (1 : Real))
      Measurable.of_discrete.aemeasurable
      (Filter.Eventually.of_forall fun sample =>
        sampleRowEitherViolationIndicator_mem_Icc
          x outWord inWord a sample)
  convert h using 1
  all_goals
    norm_num [centeredSampleRowEitherViolationIndicator] <;> rfl
end QEC.Coding.FiberBundle.RandomPartition
