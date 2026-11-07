-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.integral_localIncidenceReal_mul_selectedPairSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:23.385202+00:00
-- url     : https://prove2.me/submissions/352f190a-37e2-4090-bb9a-8243aac51111

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_localIncidenceReal
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_localSelectedPairSign
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_localIncidenceReal_indep_localSelectedPairSign

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r)) :
    ∫ localSample,
        localIncidenceReal localSample *
          localSelectedPairSign y z b localSample
      ∂(localDistribution r Delta hDelta).toMeasure =
      (RandomBase.incidenceProbability (4 * r) Delta).toReal *
        ((RandomBase.paritySign (y b) +
          RandomBase.paritySign (z b)) / 2) := by
  calc
    _ =
        (∫ localSample, localIncidenceReal localSample
          ∂(localDistribution r Delta hDelta).toMeasure) *
        (∫ localSample, localSelectedPairSign y z b localSample
          ∂(localDistribution r Delta hDelta).toMeasure) := by
      exact
        (localIncidenceReal_indep_localSelectedPairSign
          r Delta hDelta y z b).integral_fun_mul_eq_mul_integral
          Measurable.of_discrete.aestronglyMeasurable
          Measurable.of_discrete.aestronglyMeasurable
    _ = _ := by
      rw [integral_localIncidenceReal,
        integral_localSelectedPairSign]
end QEC.Coding.FiberBundle.RandomPartition
