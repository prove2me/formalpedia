-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.integral_paritySign_rowPairSyndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:39:16.397183+00:00
-- url     : https://prove2.me/submissions/53264db8-e4a9-4090-bb7f-6eead398cd1b

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowDistribution_variable_iIndepFun
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowDistribution_variable_hasLaw
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_paritySign_rowPairSyndrome
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_localPairSign

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    ∫ row, RandomBase.paritySign (rowPairSyndrome row y z)
      ∂(rowDistribution r Delta hDelta).toMeasure =
      ∏ b : Fin (4 * r),
        (1 -
          (RandomBase.incidenceProbability (4 * r) Delta).toReal +
          (RandomBase.incidenceProbability (4 * r) Delta).toReal *
            ((RandomBase.paritySign (y b) +
              RandomBase.paritySign (z b)) / 2)) := by
  have hIndep :
      ProbabilityTheory.iIndepFun
        (fun b (row : RowSample r) =>
          localPairSign y z b (row b))
        (rowDistribution r Delta hDelta).toMeasure :=
    (rowDistribution_variable_iIndepFun r Delta hDelta).comp
      (fun b localSample => localPairSign y z b localSample)
      (fun _b => Measurable.of_discrete)
  calc
    _ =
        ∫ row,
          ∏ b : Fin (4 * r), localPairSign y z b (row b)
          ∂(rowDistribution r Delta hDelta).toMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun row =>
        paritySign_rowPairSyndrome row y z
    _ =
        ∏ b : Fin (4 * r),
          ∫ row, localPairSign y z b (row b)
            ∂(rowDistribution r Delta hDelta).toMeasure := by
      exact hIndep.integral_fun_prod_eq_prod_integral
        (fun _b => Measurable.of_discrete.aestronglyMeasurable)
    _ =
        ∏ b : Fin (4 * r),
          ∫ localSample, localPairSign y z b localSample
            ∂(localDistribution r Delta hDelta).toMeasure := by
      apply Finset.prod_congr rfl
      intro b _hb
      exact (rowDistribution_variable_hasLaw
        r Delta hDelta b).integral_comp
        (f := localPairSign y z b)
        Measurable.of_discrete.aestronglyMeasurable
    _ = _ := by
      apply Finset.prod_congr rfl
      intro b _hb
      rw [integral_localPairSign]
end QEC.Coding.FiberBundle.RandomPartition
