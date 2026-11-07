-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.distribution_sampleRowEitherViolationIndicator_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:35:31.113241+00:00
-- url     : https://prove2.me/submissions/39f96220-a39f-4fe8-b28e-4c47d5d57316

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_row_iIndepFun

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
      Fin typeCount → Word (ZMod 2) (Fin (4 * r))) :
    ProbabilityTheory.iIndepFun
      (fun a =>
        sampleRowEitherViolationIndicator x outWord inWord a)
      (distribution r Delta hDelta).toMeasure := by
  exact (distribution_row_iIndepFun r Delta hDelta).comp
    (fun a row =>
      rowEitherViolationIndicator x
        (outWord (RandomTwist.checkType typeCount a))
        (inWord (RandomTwist.checkType typeCount a)) row)
    (fun _a => Measurable.of_discrete)
end QEC.Coding.FiberBundle.RandomPartition
