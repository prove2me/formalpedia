-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.initialFiberBundle_boundedLocality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:28:48.019654+00:00
-- url     : https://prove2.me/submissions/f3bc92a2-5fb9-4cc1-8c1b-f68e7e658252

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_canonicalBasisWord_eq_single
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_HammingWeight_randomFiberBundle_base_row_eq_checkDegree
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_HammingWeight_randomFiberBundle_base_col_eq_variableDegree
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary1_single_inl_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary1_single_inr_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary2_single_le
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_cycleBoundary_col_le_two
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_cycleBoundary_row_le_two
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary1_single_le
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary2_single_inl_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary2_single_inr_eq
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_baseSupportRelation_randomFiberBundleData_iff
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_bitNeighbor_incidenceRelation
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_checkNeighbor_incidenceRelation
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_baseSample_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_isTail_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_typeTwist_twistSample
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
import Theorems.Thm_QEC_Coding_FiberBundle_chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inl
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inr
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
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
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.baseSupportRelation_randomFiberBundleData_iff
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.card_bitNeighbor_incidenceRelation
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.card_checkNeighbor_incidenceRelation
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.baseSample_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.isTail_twistSample
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.typeTwist_twistSample
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
attribute [local simp] QEC.Coding.FiberBundle.homologyBaseProjection_add
attribute [local simp] QEC.Coding.FiberBundle.mem_horizontalBoundaryShadow_iff
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inl
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inr
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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open QEC.Coding
open QEC.Coding.FiberBundle.RandomBase
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDegree : HasDegreeWindows (Delta := Delta) baseSample) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplex
          (RandomTwist.fiberBundleData
            baseSample twistSample))).localityProfile
      (101 * Delta + 2) := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let X := chainComplex D
  have hLocal : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile
      (max (101 * Delta + 2) (101 * Delta + 2)) := by
    apply QEC.QLDPC.chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
        X (w := 101 * Delta + 2) (variableDegree := 101 * Delta + 2)
    · intro a
      rcases a with ⟨a, i⟩
      change HammingWeight
        (wordLinearMapTranspose (boundary1 D)
          (canonicalBasisWord (F := ZMod 2) (a, i))) ≤ 101 * Delta + 2
      rw [canonicalBasisWord_eq_single]
      apply HammingWeight_transpose_boundary1_single_le
        D (B := 101 * Delta) (F := 2) a i
      · rw [HammingWeight_randomFiberBundle_base_row_eq_checkDegree]
        have h := (hDegree.1 a).2
        omega
      · exact HammingWeight_cycleBoundary_row_le_two (ell * ell) i
    · intro b
      rcases b with ⟨b, j⟩
      change HammingWeight
        (boundary2 D (canonicalBasisWord (F := ZMod 2) (b, j))) ≤
          101 * Delta + 2
      rw [canonicalBasisWord_eq_single]
      have hBound := HammingWeight_boundary2_single_le
        D (B := 101 * Delta) (F := 2) b j
        (by
          rw [HammingWeight_randomFiberBundle_base_col_eq_variableDegree]
          have h := (hDegree.2 b).2
          omega)
        (HammingWeight_cycleBoundary_col_le_two (ell * ell) j)
      omega
    · intro q
      rw [chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns]
      change HammingWeight
          (boundary1 D (canonicalBasisWord (F := ZMod 2) q)) +
        HammingWeight
          (wordLinearMapTranspose (boundary2 D)
            (canonicalBasisWord (F := ZMod 2) q)) ≤ 101 * Delta + 2
      rw [canonicalBasisWord_eq_single]
      cases q with
      | inl q =>
          rcases q with ⟨b, i⟩
          rw [HammingWeight_boundary1_single_inl_eq]
          rw [HammingWeight_transpose_boundary2_single_inl_eq]
          rw [HammingWeight_randomFiberBundle_base_col_eq_variableDegree]
          have h := (hDegree.2 b).2
          have hf : HammingWeight (fun j => D.fiberBoundary i j) ≤ 2 := by
            simpa [D, RandomTwist.fiberBundleData, multipleRotationCycleData,
              cycleData] using
              (HammingWeight_cycleBoundary_row_le_two (ell * ell) i)
          omega
      | inr q =>
          rcases q with ⟨a, j⟩
          rw [HammingWeight_boundary1_single_inr_eq]
          rw [HammingWeight_transpose_boundary2_single_inr_eq]
          rw [HammingWeight_randomFiberBundle_base_row_eq_checkDegree]
          have h := (hDegree.1 a).2
          have hf : HammingWeight (fun i => D.fiberBoundary i j) ≤ 2 := by
            simpa [D, RandomTwist.fiberBundleData, multipleRotationCycleData,
              cycleData] using
              (HammingWeight_cycleBoundary_col_le_two (ell * ell) j)
          omega
  simpa only [max_self, X, D] using hLocal
end QEC.Coding.FiberBundle.RandomBase
