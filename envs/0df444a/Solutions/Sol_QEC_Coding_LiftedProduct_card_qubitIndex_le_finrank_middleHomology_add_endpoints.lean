-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.card_qubitIndex_le_finrank_middleHomology_add_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:29:15.090916+00:00
-- url     : https://prove2.me/submissions/08edde46-be8f-4429-9bf9-9527185b9c42

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Theorems.Thm_QEC_Coding_ChainComplexData_finrank_middleHomology_eq
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v
namespace QEC.Coding.LiftedProduct
theorem _root_.solution
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    Fintype.card (QubitIndex aRow aCol bRow bCol G) ≤
      Module.finrank F (chainComplex D).middleHomology +
        Fintype.card (C0Index aRow bRow G) +
        Fintype.card (C2Index aCol bCol G) := by
  let K := chainComplex D
  change Fintype.card (QubitIndex aRow aCol bRow bCol G) ≤
    Module.finrank F K.middleHomology +
      Fintype.card (C0Index aRow bRow G) +
      Fintype.card (C2Index aCol bCol G)
  have hRankNullity := K.boundary1.finrank_range_add_finrank_ker
  have hRankNullity2 := K.boundary2.finrank_range_add_finrank_ker
  have hRange1 : Module.finrank F (LinearMap.range K.boundary1) ≤
      Fintype.card (C0Index aRow bRow G) := by
    calc
      Module.finrank F (LinearMap.range K.boundary1) ≤
          Module.finrank F (Word F (C0Index aRow bRow G)) :=
        Submodule.finrank_le _
      _ = _ := finrank_word_eq_length
  have hRange2 : Module.finrank F (LinearMap.range K.boundary2) ≤
      Fintype.card (C2Index aCol bCol G) := by
    change Module.finrank F (LinearMap.range K.boundary2) +
      Module.finrank F (LinearMap.ker K.boundary2) =
      Module.finrank F (Word F (C2Index aCol bCol G)) at hRankNullity2
    rw [finrank_word_eq_length] at hRankNullity2
    simp only [Length] at hRankNullity2
    omega
  have hBoundaryLeCycle : Module.finrank F (LinearMap.range K.boundary2) ≤
      Module.finrank F (LinearMap.ker K.boundary1) :=
    Submodule.finrank_mono K.middleBoundaryCode_le_middleCycleCode
  have hHomology := K.finrank_middleHomology_eq
  change Module.finrank F (LinearMap.range K.boundary1) +
    Module.finrank F (LinearMap.ker K.boundary1) =
    Module.finrank F (Word F (QubitIndex aRow aCol bRow bCol G)) at hRankNullity
  rw [finrank_word_eq_length] at hRankNullity
  simp only [Length] at hRankNullity
  change Module.finrank F K.middleHomology =
    Module.finrank F (LinearMap.ker K.boundary1) -
      Module.finrank F (LinearMap.range K.boundary2) at hHomology
  omega
end QEC.Coding.LiftedProduct
