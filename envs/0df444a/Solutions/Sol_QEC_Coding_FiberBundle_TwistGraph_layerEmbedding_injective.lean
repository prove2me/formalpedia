-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.layerEmbedding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:52:04.768735+00:00
-- url     : https://prove2.me/submissions/e2249842-ad10-4402-b3bb-1c4fa575d883

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
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
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    (ell : Nat) [NeZero ell] :
    Function.Injective (layerEmbedding ell) := by
  by_cases hOne : ell = 1
  · subst ell
    intro u v _huv
    exact Subsingleton.elim u v
  intro u v huv
  apply ZMod.val_injective ell
  have hnat :
      (u.val : ZMod (ell * ell)) * (ell : ZMod (ell * ell)) =
        (v.val : ZMod (ell * ell)) * (ell : ZMod (ell * ell)) := by
    simpa only [layerEmbedding_eq_val_mul, Nat.cast_mul] using huv
  have hell : 0 < ell := NeZero.pos ell
  have htwo : 2 ≤ ell := by omega
  have huCast :
      (u.val : ZMod (ell * ell)).val = u.val := by
    rw [ZMod.val_natCast_of_lt]
    nlinarith [u.val_lt]
  have hvCast :
      (v.val : ZMod (ell * ell)).val = v.val := by
    rw [ZMod.val_natCast_of_lt]
    nlinarith [v.val_lt]
  have hellCast :
      (ell : ZMod (ell * ell)).val = ell := by
    rw [ZMod.val_natCast_of_lt]
    nlinarith
  have huBound : u.val * ell < ell * ell := by
    nlinarith [u.val_lt]
  have hvBound : v.val * ell < ell * ell := by
    nlinarith [v.val_lt]
  have huMulBound :
      (u.val : ZMod (ell * ell)).val *
          (ell : ZMod (ell * ell)).val < ell * ell := by
    simpa only [huCast, hellCast] using huBound
  have hvMulBound :
      (v.val : ZMod (ell * ell)).val *
          (ell : ZMod (ell * ell)).val < ell * ell := by
    simpa only [hvCast, hellCast] using hvBound
  have hval := congrArg ZMod.val hnat
  rw [ZMod.val_mul_of_lt huMulBound,
    ZMod.val_mul_of_lt hvMulBound,
    huCast, hvCast, hellCast] at hval
  exact Nat.eq_of_mul_eq_mul_right hell hval
end QEC.Coding.FiberBundle.TwistGraph
