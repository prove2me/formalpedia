-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.qubitDegree_inr_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:36:28.212677+00:00
-- url     : https://prove2.me/submissions/09e3abb9-e260-4976-a18e-8e2ed12f38e6

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
private theorem hammingWeight_neg
    {F A : Type*} [AddGroup F] [DecidableEq F] [Fintype A]
    (x : Word F A) :
    HammingWeight (fun a => -x a) = HammingWeight x := by
  classical
  unfold HammingWeight hammingSupport
  congr 1
  ext a
  simp
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
    (r₁ : rowOne) (r₂ : rowTwo) :
    qubitDegree D (Sum.inr (r₁, r₂)) =
      rowWeight D.second r₂ + rowWeight D.first r₁ := by
  rw [qubitDegree, boundary1, toLin_single, boundary2,
    wordLinearMapTranspose_toLin_single]
  change
    HammingWeight
        (fun p : rowOne × colTwo =>
          if p.1 = r₁ then -D.second r₂ p.2 else 0) +
      HammingWeight
        (fun p : colOne × rowTwo =>
          if r₂ = p.2 then D.first r₁ p.1 else 0) = _
  rw [show HammingWeight
      (fun p : rowOne × colTwo =>
        if p.1 = r₁ then -D.second r₂ p.2 else 0) =
      rowWeight D.second r₂ by
        calc
          HammingWeight
              (fun p : rowOne × colTwo =>
                if p.1 = r₁ then -D.second r₂ p.2 else 0) =
              HammingWeight (fun c₂ => -D.second r₂ c₂) := by
                simpa [eq_comm] using
                  hammingWeight_fixed_first r₁
                    (fun c₂ => -D.second r₂ c₂)
          _ = HammingWeight (D.second r₂) := hammingWeight_neg (D.second r₂)
          _ = rowWeight D.second r₂ := rfl]
  rw [show HammingWeight
      (fun p : colOne × rowTwo =>
        if r₂ = p.2 then D.first r₁ p.1 else 0) =
      rowWeight D.first r₁ by
        simpa [rowWeight] using
          hammingWeight_fixed_second r₂ (D.first r₁)]
end QEC.Coding.HypergraphProduct
