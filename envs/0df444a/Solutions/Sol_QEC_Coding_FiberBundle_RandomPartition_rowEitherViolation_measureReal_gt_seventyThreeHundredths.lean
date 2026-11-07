-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.rowEitherViolation_measureReal_gt_seventyThreeHundredths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:45:27.549192+00:00
-- url     : https://prove2.me/submissions/a4d13dd6-bbd0-42ff-8a67-a0ed3e0c9aec

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_baseSample_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_isTail_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_typeTwist_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_incidenceProbability_toReal_le_half
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_paritySign_rowPairSyndrome_le_exp
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowEitherViolation_measureReal
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_delta_mul_four_r_le_xorPairWeight
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_four_le_incidenceProbability_mul_weight
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exp_neg_four_lt_one_fiftieth
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_conj_stdAddChar_neg
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_heavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_lightLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_mediumLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_nonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_twoSidedLightTypeSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_eq_add
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_inNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.blockEquiv_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.conj_stdAddChar_neg
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_eq_sub
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badHeavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_heavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_lightLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_mediumLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_nonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_twoSidedLightTypeSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableHeavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.baseSample_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.isTail_twistSample
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.typeTwist_twistSample

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hOut : Delta * HammingWeight outWord ≤ 2 * (4 * r))
    (hIn : Delta * HammingWeight inWord ≤ 2 * (4 * r)) :
    (73 : Real) / 100 <
      (rowDistribution r Delta (by omega)).toMeasure.real
        {row |
          rowPairSyndrome row x outWord ≠ 0 ∨
          rowPairSyndrome row inWord x ≠ 0} := by
  let p : Real :=
    (RandomBase.incidenceProbability (4 * r) Delta).toReal
  have hpHalf : p ≤ 1 / 2 :=
    incidenceProbability_toReal_le_half r Delta hDeltaHalf
  have hFirstScale :
      (4 : Real) ≤ p *
        ((HammingWeight x : Real) + HammingWeight outWord) := by
    have h :=
      four_le_incidenceProbability_mul_weight
        r Delta (HammingWeight x + HammingWeight outWord) hr
        (le_trans hx
          (Nat.mul_le_mul_left Delta (Nat.le_add_right _ _)))
    simpa [p, Nat.cast_add] using h
  have hSecondScale :
      (4 : Real) ≤ p *
        ((HammingWeight inWord : Real) + HammingWeight x) := by
    have h :
        4 * (4 * r) ≤
          Delta * (HammingWeight inWord + HammingWeight x) := by
      calc
        _ ≤ Delta * HammingWeight x := hx
        _ ≤ _ :=
          Nat.mul_le_mul_left Delta (Nat.le_add_left _ _)
    simpa [p, Nat.cast_add] using
      four_le_incidenceProbability_mul_weight
        r Delta (HammingWeight inWord + HammingWeight x) hr h
  have hThirdNat :
      4 * (4 * r) ≤
        Delta *
          (HammingWeight (x + inWord) +
            HammingWeight (outWord + x)) :=
    delta_mul_four_r_le_xorPairWeight
      r Delta x outWord inWord hx hOut hIn
  have hThirdScale :
      (4 : Real) ≤ p *
        ((HammingWeight (x + inWord) : Real) +
          HammingWeight (outWord + x)) := by
    simpa [p, Nat.cast_add] using
      four_le_incidenceProbability_mul_weight
        r Delta
          (HammingWeight (x + inWord) +
            HammingWeight (outWord + x))
          hr hThirdNat
  have hFirstChar :
      (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row x outWord) ∂
            (rowDistribution r Delta (by omega)).toMeasure) ≤
        Real.exp (-4) := by
    calc
      _ ≤ Real.exp
          (-p * ((HammingWeight x : Real) +
            HammingWeight outWord)) :=
        integral_paritySign_rowPairSyndrome_le_exp
          r Delta (by omega) x outWord hpHalf
      _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.mpr
        linarith
  have hSecondChar :
      (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row inWord x) ∂
            (rowDistribution r Delta (by omega)).toMeasure) ≤
        Real.exp (-4) := by
    calc
      _ ≤ Real.exp
          (-p * ((HammingWeight inWord : Real) +
            HammingWeight x)) :=
        integral_paritySign_rowPairSyndrome_le_exp
          r Delta (by omega) inWord x hpHalf
      _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.mpr
        linarith
  have hThirdChar :
      (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row
              (x + inWord) (outWord + x)) ∂
            (rowDistribution r Delta (by omega)).toMeasure) ≤
        Real.exp (-4) := by
    calc
      _ ≤ Real.exp
          (-p * ((HammingWeight (x + inWord) : Real) +
            HammingWeight (outWord + x))) :=
        integral_paritySign_rowPairSyndrome_le_exp
          r Delta (by omega) (x + inWord) (outWord + x) hpHalf
      _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.mpr
        linarith
  rw [rowEitherViolation_measureReal
    r Delta (by omega) x outWord inWord]
  nlinarith [exp_neg_four_lt_one_fiftieth]
end QEC.Coding.FiberBundle.RandomPartition
