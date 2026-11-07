-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_le_firstTranspose_of_secondTranspose_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:41:39.988199+00:00
-- url     : https://prove2.me/submissions/83cd1a29-c9ea-4259-80cd-75e3acc9512d

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_UpperBound
import Theorems.Thm_QEC_Coding_HypergraphProduct_exists_nonzero_mem_of_extendedMinimumDistance_ne_top
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_exists_cohomology_witness_of_transpose_nonzero
import Theorems.Thm_QEC_Coding_HypergraphProduct_finitePredicateMinimum_le_of
import Theorems.Thm_QEC_Coding_HypergraphProduct_firstCode_transposeData
import Theorems.Thm_QEC_Coding_HypergraphProduct_jointTensorWordMap_tmul_fst_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_jointTensorWordMap_tmul_snd_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_secondTransposeCode_transposeData
import Theorems.Thm_QEC_Coding_HypergraphProduct_supportExtendedWitness_apply_mem
import Theorems.Thm_QEC_Coding_HypergraphProduct_swapWord_inl_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_swapWord_inr_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_swapWord_swapWord
import Theorems.Thm_QEC_Coding_HypergraphProduct_wordTensorEquiv_tmul_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_zeroExtend_apply_mem
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
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
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
attribute [local simp] QEC.Coding.HypergraphProduct.firstCode_transposeData
attribute [local simp] QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_fst_apply
attribute [local simp] QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_snd_apply
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.secondTransposeCode_transposeData
attribute [local simp] QEC.Coding.HypergraphProduct.supportExtendedWitness_apply_mem
attribute [local simp] QEC.Coding.HypergraphProduct.swapWord_inl_apply
attribute [local simp] QEC.Coding.HypergraphProduct.swapWord_inr_apply
attribute [local simp] QEC.Coding.HypergraphProduct.swapWord_swapWord
attribute [local simp] QEC.Coding.HypergraphProduct.wordTensorEquiv_tmul_apply
attribute [local simp] QEC.Coding.HypergraphProduct.zeroExtend_apply_mem
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
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
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hSecondTranspose :
      extendedMinimumDistance (secondTransposeCode D) ≠ ⊤) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
      extendedMinimumDistance (firstTransposeCode D) := by
  classical
  obtain ⟨y, hy, hy0⟩ :=
    exists_nonzero_mem_of_extendedMinimumDistance_ne_top
      (secondTransposeCode D) hSecondTranspose
  rw [extendedMinimumDistance, finitePredicateMinimum]
  apply Finset.le_inf
  intro x _hxUniv
  by_cases hx : x ∈ (firstTransposeCode D).carrier ∧ x ≠ 0
  · obtain ⟨z, hzCocycle, hzNotCoboundary, hzWeight⟩ :=
      exists_cohomology_witness_of_transpose_nonzero
        D x hx.1 hx.2 y hy hy0
    have hzLogical :
        IsCSSLogical (binaryCSSCode D).xCode (binaryCSSCode D).zCode z :=
      Or.inl ⟨by
          simpa only [binaryCSSCode_zCode,
            ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
            using hzCocycle,
        by simpa only [binaryCSSCode_xCode] using hzNotCoboundary⟩
    calc
      extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
          (HammingWeight z : WithTop Nat) := by
        rw [extendedAlgebraicCSSMinimumDistance]
        exact finitePredicateMinimum_le_of hzLogical
      _ = (HammingWeight x : WithTop Nat) := by rw [hzWeight]
      _ = if x ∈ (firstTransposeCode D).carrier ∧ x ≠ 0 then
          (HammingWeight x : WithTop Nat) else ⊤ := by simp [hx]
  · split
    · next hMatrix =>
        exfalso
        apply hx
        exact ⟨(mem_firstTransposeCode_iff D x).2 hMatrix.1, hMatrix.2⟩
    · exact le_top
end QEC.Coding.HypergraphProduct
