-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.qubitDegree_inl_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:36:18.264228+00:00
-- url     : https://prove2.me/submissions/79945282-52d9-4b07-8a27-0b22f6e7cb82

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Theorems.Thm_QEC_Coding_HypergraphProduct_hammingWeight_fixed_first
import Theorems.Thm_QEC_Coding_HypergraphProduct_hammingWeight_fixed_second
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
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
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
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


section
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
private theorem wordLinearMapTranspose_toLin_single
    {F Row Col : Type*} [Field F] [Fintype F]
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : Matrix Row Col F) (r : Row) :
    wordLinearMapTranspose (Matrix.toLin' M) (Pi.single r 1) =
      fun c => M r c := by
  ext c
  unfold wordLinearMapTranspose
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_eq_single r]
  · simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _hc' hne
      simp [hne]
    · simp
  · intro r' hr'
    simp [hr']
private theorem toLin_single
    {F Row Col : Type*} [Field F]
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : Matrix Row Col F) (c : Col) :
    Matrix.toLin' M (Pi.single c 1) = fun r => M r c := by
  ext r
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _hc' hne
    simp [hne]
  · simp
end QEC.Coding.HypergraphProduct
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (c₁ : colOne) (c₂ : colTwo) :
    qubitDegree D (Sum.inl (c₁, c₂)) =
      columnWeight D.first c₁ + columnWeight D.second c₂ := by
  rw [qubitDegree, boundary1, toLin_single, boundary2,
    wordLinearMapTranspose_toLin_single]
  change
    HammingWeight
        (fun p : rowOne × colTwo =>
          if p.2 = c₂ then D.first p.1 c₁ else 0) +
      HammingWeight
        (fun p : colOne × rowTwo =>
          if c₁ = p.1 then D.second p.2 c₂ else 0) = _
  rw [show HammingWeight
      (fun p : rowOne × colTwo =>
        if p.2 = c₂ then D.first p.1 c₁ else 0) =
      columnWeight D.first c₁ by
        simpa [eq_comm, columnWeight] using
          hammingWeight_fixed_second c₂ (fun r₁ => D.first r₁ c₁)]
  rw [show HammingWeight
      (fun p : colOne × rowTwo =>
        if c₁ = p.1 then D.second p.2 c₂ else 0) =
      columnWeight D.second c₂ by
        simpa [columnWeight] using
          hammingWeight_fixed_first c₁ (fun r₂ => D.second r₂ c₂)]
end QEC.Coding.HypergraphProduct
