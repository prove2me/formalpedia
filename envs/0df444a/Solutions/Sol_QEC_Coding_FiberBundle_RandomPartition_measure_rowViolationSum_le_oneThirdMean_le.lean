-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.measure_rowViolationSum_le_oneThirdMean_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:39:05.661585+00:00
-- url     : https://prove2.me/submissions/cabe7e17-226f-4fd7-ac5c-aaf5809becdc

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_baseSample_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_isTail_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_typeTwist_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_mgf_sum_sampleRowViolationIndicator
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
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (rows : Finset (Fin (3 * r))) :
    let μ :=
      (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0}
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            sampleRowViolationIndicator y z a sample) ≤
              μ * rows.card / 3} ≤
      Real.exp (-(μ * rows.card) / 6) := by
  dsimp only
  let μ : Real :=
    (rowDistribution r Delta hDelta).toMeasure.real
      {row | rowPairSyndrome row y z ≠ 0}
  let count : Sample r → Real :=
    fun sample =>
      ∑ a ∈ rows, sampleRowViolationIndicator y z a sample
  have hμ0 : 0 ≤ μ := measureReal_nonneg
  have hμ1 : μ ≤ 1 := measureReal_le_one
  have hExpHalf : Real.exp (-1) ≤ (1 : Real) / 2 := by
    rw [Real.exp_neg]
    have hTwoExp : (2 : Real) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1 : Real)]
    simpa [one_div] using
      (inv_le_inv₀ (Real.exp_pos 1)
        (by norm_num : (0 : Real) < 2)).2 hTwoExp
  have hBase0 : 0 ≤ 1 - μ + μ * Real.exp (-1) := by
    nlinarith [Real.exp_pos (-1)]
  have hBaseExp :
      1 - μ + μ * Real.exp (-1) ≤
        Real.exp (μ * (Real.exp (-1) - 1)) := by
    convert Real.add_one_le_exp
      (μ * (Real.exp (-1) - 1)) using 1
    ring
  have hPow :
      (1 - μ + μ * Real.exp (-1)) ^ rows.card ≤
        Real.exp
          ((rows.card : Real) *
            (μ * (Real.exp (-1) - 1))) := by
    calc
      _ ≤ (Real.exp (μ * (Real.exp (-1) - 1))) ^ rows.card :=
        pow_le_pow_left₀ hBase0 hBaseExp rows.card
      _ = _ := by rw [Real.exp_nat_mul]
  have hChernoff :
      (distribution r Delta hDelta).toMeasure.real
          {sample | count sample ≤ μ * rows.card / 3} ≤
        Real.exp (-(-1 : Real) * (μ * rows.card / 3)) *
          ProbabilityTheory.mgf count
            (distribution r Delta hDelta).toMeasure (-1) := by
    exact ProbabilityTheory.measure_le_le_exp_mul_mgf
      (X := count) (μ * rows.card / 3)
      (show (-1 : Real) ≤ 0 by norm_num)
      Integrable.of_finite
  calc
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            sampleRowViolationIndicator y z a sample) ≤
              μ * rows.card / 3} =
        (distribution r Delta hDelta).toMeasure.real
          {sample | count sample ≤ μ * rows.card / 3} := rfl
    _ ≤ Real.exp (-(-1 : Real) * (μ * rows.card / 3)) *
          ProbabilityTheory.mgf count
            (distribution r Delta hDelta).toMeasure (-1) :=
      hChernoff
    _ =
        Real.exp (μ * rows.card / 3) *
          (1 - μ + μ * Real.exp (-1)) ^ rows.card := by
      rw [show ProbabilityTheory.mgf count
          (distribution r Delta hDelta).toMeasure (-1) =
        (1 - μ + μ * Real.exp (-1)) ^ rows.card by
          simpa [count, μ] using
            mgf_sum_sampleRowViolationIndicator
              r Delta hDelta y z rows (-1)]
      congr 2
      ring
    _ ≤
        Real.exp (μ * rows.card / 3) *
          Real.exp
            ((rows.card : Real) *
              (μ * (Real.exp (-1) - 1))) := by
      exact mul_le_mul_of_nonneg_left hPow (Real.exp_pos _).le
    _ =
        Real.exp
          (μ * rows.card / 3 +
            (rows.card : Real) *
              (μ * (Real.exp (-1) - 1))) := by
      rw [Real.exp_add]
    _ ≤ Real.exp (-(μ * rows.card) / 6) := by
      apply Real.exp_le_exp_of_le
      have hRows0 : (0 : Real) ≤ rows.card := by positivity
      have hmul :
          μ * (rows.card : Real) * Real.exp (-1) ≤
            μ * (rows.card : Real) / 2 := by
        calc
          _ ≤ μ * (rows.card : Real) * ((1 : Real) / 2) :=
            mul_le_mul_of_nonneg_left hExpHalf
              (mul_nonneg hμ0 hRows0)
          _ = _ := by ring
      nlinarith
end QEC.Coding.FiberBundle.RandomPartition
