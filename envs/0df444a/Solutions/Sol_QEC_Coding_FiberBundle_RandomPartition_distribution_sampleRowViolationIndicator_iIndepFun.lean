-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.distribution_sampleRowViolationIndicator_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:22:13.848884+00:00
-- url     : https://prove2.me/submissions/0b3eb842-f3f6-4b63-b597-6146ac98e6fb

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
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    ProbabilityTheory.iIndepFun
      (fun a => sampleRowViolationIndicator y z a)
      (distribution r Delta hDelta).toMeasure := by
  exact (distribution_row_iIndepFun r Delta hDelta).comp
    (fun _a row => rowViolationIndicator y z row)
    (fun _a => Measurable.of_discrete)
end QEC.Coding.FiberBundle.RandomPartition
