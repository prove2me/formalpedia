-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.exists_fullyGood_hho20_base_and_twist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:33:06.806766+00:00
-- url     : https://prove2.me/submissions/e1993e60-2419-4a77-8c40-b07c4ed442a2

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exists_sample_isFullyGood_and_hasHHO20PartitionedChecks
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hasHHO20CayleySpectrum_twistSample_typeTwist
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_exists_twistSample_hasHHO20CayleySpectrum
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hasHHO20EdgeMixing_of_squaredExpanderMixing
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hasHHO20LayerMixing_of_edgeMixing
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hasHHO20LocalTestability_of_partitionedChecks_and_layerMixing
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hasHHO20OperatorMixing_of_cayleySpectrum
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hasHHO20SquaredExpanderMixing_of_operatorMixing


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount ell : Nat)
    [NeZero r] [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hDeltaForty : 40 ≤ Delta)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hHeavyScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (hEll : 100001 ≤ ell)
    (hTypeCountSpectrum :
      (40000000000 : Real) * Real.log (ell : Real) ≤
        (typeCount : Real))
    (hNumeric :
      (fullyGoodBaseFailureBound r Delta).toReal +
          ((typeCount : Real) *
              ((1 +
                Real.exp
                  (-(Delta : Real) / (200 * typeCount))) ^
                    (8 * r) - 1) +
            Real.exp (-(r : Real) / 10)) <
        1) :
    ∃ (baseSample : RandomBase.Sample r)
        (twistSample : RandomTwist.Sample r typeCount ell),
      RandomBase.IsFullyGood
          (Delta := Delta) baseSample ∧
        TwistGraph.HasHHO20PartitionedChecks
          Delta baseSample twistSample ∧
        TwistGraph.HasHHO20CayleySpectrum twistSample ∧
        TwistGraph.HasHHO20LocalTestability
          Delta baseSample twistSample := by
  obtain ⟨spectrumSample, hSpectrumSample⟩ :=
    TwistGraph.exists_twistSample_hasHHO20CayleySpectrum
      r typeCount ell hEll hTypeCountSpectrum
  let typeShifts : Fin typeCount → Fin (ell - 1) :=
    fun τ => RandomTwist.typeTwist spectrumSample τ
  obtain ⟨partitionSample, hBase, hChecks⟩ :=
    exists_sample_isFullyGood_and_hasHHO20PartitionedChecks
      r Delta typeCount ell hr hDeltaHalf hTypeDvd
      hDelta hDeltaOne hTypeSmall hHeavyScale
      typeShifts hNumeric
  let assembledTwist :=
    twistSample partitionSample typeShifts
  have hSpectrum :
      TwistGraph.HasHHO20CayleySpectrum assembledTwist := by
    exact hasHHO20CayleySpectrum_twistSample_typeTwist
      partitionSample spectrumSample hSpectrumSample
  have hOperator :
      TwistGraph.HasHHO20OperatorMixing assembledTwist :=
    TwistGraph.hasHHO20OperatorMixing_of_cayleySpectrum
      assembledTwist hSpectrum
  have hSquared :
      TwistGraph.HasHHO20SquaredExpanderMixing assembledTwist :=
    TwistGraph.hasHHO20SquaredExpanderMixing_of_operatorMixing
      assembledTwist hOperator
  have hEdge :
      TwistGraph.HasHHO20EdgeMixing Delta assembledTwist :=
    TwistGraph.hasHHO20EdgeMixing_of_squaredExpanderMixing
      Delta assembledTwist hSquared
  have hLayer :
      TwistGraph.HasHHO20LayerMixing Delta assembledTwist :=
    TwistGraph.hasHHO20LayerMixing_of_edgeMixing
      Delta assembledTwist hEdge
  have hLocal :
      TwistGraph.HasHHO20LocalTestability
        Delta (baseSample partitionSample) assembledTwist :=
    TwistGraph.hasHHO20LocalTestability_of_partitionedChecks_and_layerMixing
      Delta (baseSample partitionSample) assembledTwist
      hDeltaForty hChecks hLayer
  exact
    ⟨baseSample partitionSample, assembledTwist,
      hBase, hChecks, hSpectrum, hLocal⟩
end QEC.Coding.FiberBundle.RandomPartition
