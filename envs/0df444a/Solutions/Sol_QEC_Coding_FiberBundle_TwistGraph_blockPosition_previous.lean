-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.blockPosition_previous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:52:05.542896+00:00
-- url     : https://prove2.me/submissions/d588d835-0473-4f24-abd2-a540350dc002

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
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


attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.blockEquiv_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (u : ZMod ell) :
    blockPosition ell
        (u - 1, ⟨ell - 1,
          Nat.sub_lt (NeZero.pos ell) Nat.zero_lt_one⟩) =
      layerEmbedding ell u - 1 := by
  have hEllPos : 0 < ell := NeZero.pos ell
  rw [blockPosition]
  change
    layerEmbedding ell (u - 1) +
        ((ell - 1 : Nat) : ZMod (ell * ell)) =
      layerEmbedding ell u - 1
  rw [map_sub]
  have hOne :
      layerEmbedding ell (1 : ZMod ell) =
        (ell : Nat) := by
    simpa using layerEmbedding_natCast ell 1
  rw [hOne]
  have hEllCast :
      ((ell : Nat) : ZMod (ell * ell)) =
        ((ell - 1 : Nat) : ZMod (ell * ell)) + 1 := by
    calc
      ((ell : Nat) : ZMod (ell * ell)) =
          (((ell - 1) + 1 : Nat) : ZMod (ell * ell)) := by
            congr 1
            omega
      _ = ((ell - 1 : Nat) : ZMod (ell * ell)) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
  rw [hEllCast]
  abel
end QEC.Coding.FiberBundle.TwistGraph
