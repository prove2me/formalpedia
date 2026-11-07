-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.boundary1TransposeTensorMap_eq_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:41:25.464707+00:00
-- url     : https://prove2.me/submissions/79479e14-c485-4e10-b4a1-6b4d10d5e701

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Realization
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Theorems.Thm_QEC_Coding_HypergraphProduct_boundary1Transpose_inl_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_boundary1Transpose_inr_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_jointTensorWordMap_tmul_fst_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_jointTensorWordMap_tmul_snd_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_wordTensorEquiv_tmul_apply
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
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.wordTensorEquiv_tmul_apply
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


attribute [local simp] QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_fst_apply
attribute [local simp] QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_snd_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    boundary1TransposeTensorMap D =
      jointTensorWordMap (Matrix.toLin' D.first.transpose)
        (Matrix.toLin' D.second) := by
  apply TensorProduct.ext'
  intro x y
  apply Prod.ext
  · funext q
    rcases q with ⟨c₁, c₂⟩
    change wordLinearMapTranspose (boundary1 D)
        (wordTensorEquiv (ZMod 2) rowOne colTwo (x ⊗ₜ[ZMod 2] y))
        (Sum.inl (c₁, c₂)) = _
    calc
      _ = ∑ r₁ : rowOne,
          wordTensorEquiv (ZMod 2) rowOne colTwo
              (x ⊗ₜ[ZMod 2] y) (r₁, c₂) * D.first r₁ c₁ :=
        boundary1Transpose_inl_apply D _ c₁ c₂
      _ = _ := by
        simp only [wordTensorEquiv_tmul_apply,
          jointTensorWordMap_tmul_fst_apply, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct, Matrix.transpose_apply]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r₁ _hr₁
        ring
  · funext q
    rcases q with ⟨r₁, r₂⟩
    change wordLinearMapTranspose (boundary1 D)
        (wordTensorEquiv (ZMod 2) rowOne colTwo (x ⊗ₜ[ZMod 2] y))
        (Sum.inr (r₁, r₂)) = _
    calc
      _ = -∑ c₂ : colTwo,
          wordTensorEquiv (ZMod 2) rowOne colTwo
              (x ⊗ₜ[ZMod 2] y) (r₁, c₂) * D.second r₂ c₂ :=
        boundary1Transpose_inr_apply D _ r₁ r₂
      _ = _ := by
        simp only [wordTensorEquiv_tmul_apply,
          jointTensorWordMap_tmul_snd_apply, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct]
        rw [ZMod.neg_eq_self_mod_two, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c₂ _hc₂
        ring
end QEC.Coding.HypergraphProduct
