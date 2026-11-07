-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.distribution_incidence_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:22.561218+00:00
-- url     : https://prove2.me/submissions/b39d9b76-0535-4bce-96bd-c3ff55384233

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_row_iIndepFun
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_fixedRow_incidence_iIndepFun

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun edge : Fin (3 * r) × Fin (4 * r) =>
        fun sample : Sample r => sample edge.1 edge.2 false)
      (distribution r Delta hDelta).toMeasure := by
  have hOuter :
      ProbabilityTheory.iIndepFun
        (fun a (sample : Sample r) => fun b => sample a b false)
        (distribution r Delta hDelta).toMeasure :=
    (distribution_row_iIndepFun r Delta hDelta).comp
      (fun _a row => fun b => row b false)
      (fun _a => Measurable.of_discrete)
  exact ProbabilityTheory.iIndepFun_uncurry'
    (fun _a _b => Measurable.of_discrete)
    hOuter
    (distribution_fixedRow_incidence_iIndepFun r Delta hDelta)
end QEC.Coding.FiberBundle.RandomPartition
