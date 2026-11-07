-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.measure_heavyEitherViolationSum_le_r_div_twentyFive_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:50:11.701291+00:00
-- url     : https://prove2.me/submissions/9111b7e5-9965-4e26-b243-7bf09cbf4518

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_baseSample_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_isTail_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_typeTwist_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_centeredRowEitherViolationSum_le_neg_le
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_seventyThreeHundredths_mul_card_le_sum_heavyRowMeans
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sum_centeredSampleRowEitherViolationIndicator_eq
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_selectedTypeRows_card_bounds
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
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (types : Finset (Fin typeCount))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hTypes : 98 * typeCount ≤ 100 * types.card)
    (hNeighbors :
      ∀ τ ∈ types,
        Delta * HammingWeight (outWord τ) ≤ 2 * (4 * r) ∧
        Delta * HammingWeight (inWord τ) ≤ 2 * (4 * r)) :
    let rows := selectedTypeRows r typeCount types
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            sampleRowEitherViolationIndicator
              x outWord inWord a sample) ≤
            (r : Real) / 25} ≤
      Real.exp (-3 * (r : Real)) := by
  dsimp only
  let hDelta : Delta ≤ 4 * r := by omega
  let rows := selectedTypeRows r typeCount types
  have hBounds :
      294 * r ≤ 100 * rows.card ∧ rows.card ≤ 3 * r := by
    exact selectedTypeRows_card_bounds
      r typeCount hTypeDvd types hTypes
  have hRowsPos : 0 < rows.card := by omega
  have hMean :
      (73 : Real) / 100 * rows.card ≤
        ∑ a ∈ rows,
          ∫ sample,
            sampleRowEitherViolationIndicator
              x outWord inWord a sample ∂
              (distribution r Delta hDelta).toMeasure := by
    simpa [rows, hDelta] using
      seventyThreeHundredths_mul_card_le_sum_heavyRowMeans
        r Delta typeCount hr hDeltaHalf x types
        outWord inWord hx hNeighbors
  let ε : Real := (73 : Real) / 100 * rows.card - r / 25
  have hBoundsReal :
      (294 : Real) * r ≤ 100 * rows.card ∧
        (rows.card : Real) ≤ 3 * r := by
    constructor
    · exact_mod_cast hBounds.1
    · exact_mod_cast hBounds.2
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hSubset :
      {sample |
        (∑ a ∈ rows,
          sampleRowEitherViolationIndicator
            x outWord inWord a sample) ≤
          (r : Real) / 25} ⊆
        {sample |
          (∑ a ∈ rows,
            centeredSampleRowEitherViolationIndicator
              Delta hDelta x outWord inWord a sample) ≤ -ε} := by
    intro sample hLow
    change
      (∑ a ∈ rows,
        sampleRowEitherViolationIndicator
          x outWord inWord a sample) ≤
        (r : Real) / 25 at hLow
    change
      (∑ a ∈ rows,
        centeredSampleRowEitherViolationIndicator
          Delta hDelta x outWord inWord a sample) ≤ -ε
    rw [sum_centeredSampleRowEitherViolationIndicator_eq
      r Delta typeCount hDelta x outWord inWord rows sample]
    dsimp [ε]
    linarith
  calc
    _ ≤
        (distribution r Delta hDelta).toMeasure.real
          {sample |
            (∑ a ∈ rows,
              centeredSampleRowEitherViolationIndicator
                Delta hDelta x outWord inWord a sample) ≤ -ε} :=
      measureReal_mono hSubset
    _ ≤
        Real.exp
          (-(ε ^ 2) /
            (2 * ↑(∑ _a ∈ rows, (1 / 4 : NNReal)))) :=
      measure_centeredRowEitherViolationSum_le_neg_le
        r Delta typeCount hDelta x outWord inWord rows ε (le_of_lt hε)
    _ ≤ Real.exp (-3 * (r : Real)) := by
      apply Real.exp_le_exp.mpr
      have hSum :
          (↑(∑ _a ∈ rows, (1 / 4 : NNReal)) : Real) =
            (rows.card : Real) / 4 := by
        simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      rw [hSum]
      have hRowsReal : (0 : Real) < rows.card := by
        exact_mod_cast hRowsPos
      dsimp [ε]
      rw [div_le_iff₀ (by positivity : (0 : Real) <
        2 * ((rows.card : Real) / 4))]
      nlinarith [sq_nonneg
        ((73 : Real) / 100 * rows.card - r / 25)]
end QEC.Coding.FiberBundle.RandomPartition
