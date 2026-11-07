-- Prove2me | solution 1 for QEC.Coding.FiberBundle.cycleFiberCoboundary_cycleFiberPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:34:19.842172+00:00
-- url     : https://prove2.me/submissions/077174af-d2d5-4aa8-90a6-948b1dfc7336

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_zmodFinEquiv_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberCoboundary_apply
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
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (g : Word (ZMod 2) (ZMod n))
    (hg : (∑ j : ZMod n, g j) = 0) :
    cycleFiberCoboundary n (cycleFiberPrimitive n g) = g := by
  letI : Fact (1 < n) := ⟨by omega⟩
  have honeVal : (1 : ZMod n).val = 1 := by
    exact ZMod.val_one n
  funext j
  rw [cycleFiberCoboundary_apply n hn]
  by_cases hnext : j.val + 1 < n
  · have hval : (j + 1).val = j.val + 1 := by
      rw [ZMod.val_add_of_lt]
      · rw [honeVal]
      · simpa [honeVal] using hnext
    have hjCast : (j.val : ZMod n) = j := by
      exact ZMod.natCast_zmod_val j
    rw [cycleFiberPrimitive, cycleFiberPrimitive, hval,
      Finset.sum_range_succ, hjCast]
    let a := ∑ k ∈ Finset.range j.val, g (k : ZMod n)
    change a + (a + g j) = g j
    have haa : a + a = 0 := by
      calc
        a + a = a + (-a) := by rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel a
    calc
      a + (a + g j) = (a + a) + g j := by abel
      _ = g j := by rw [haa, zero_add]
  · have hjLast : j.val + 1 = n := by
      have hjLt : j.val < n := j.val_lt
      omega
    have hval : (j + 1).val = 0 := by
      rw [ZMod.val_add]
      rw [honeVal]
      rw [hjLast, Nat.mod_self]
    have hjCast : (j.val : ZMod n) = j := by
      exact ZMod.natCast_zmod_val j
    have hsumRange :
        (∑ k ∈ Finset.range n, g (k : ZMod n)) =
          ∑ z : ZMod n, g z := by
      calc
        (∑ k ∈ Finset.range n, g (k : ZMod n)) =
            ∑ k : Fin n, g (k.val : ZMod n) := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro k hk
          simp [Finset.mem_range.mp hk]
        _ = ∑ z : ZMod n, g z := by
          apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
          intro k
          change g (k.val : ZMod n) = g (ZMod.finEquiv n k)
          rw [zmodFinEquiv_apply]
    have hprefix :
        (∑ k ∈ Finset.range j.val, g (k : ZMod n)) = g j := by
      have hrangeSucc :
          (∑ k ∈ Finset.range j.val, g (k : ZMod n)) + g j =
            ∑ k ∈ Finset.range (j.val + 1), g (k : ZMod n) := by
        rw [Finset.sum_range_succ, hjCast]
      have htotal :
          (∑ k ∈ Finset.range j.val, g (k : ZMod n)) + g j = 0 := by
        rw [hrangeSucc, hjLast, hsumRange, hg]
      calc
        (∑ k ∈ Finset.range j.val, g (k : ZMod n)) =
            -g j := eq_neg_of_add_eq_zero_left htotal
        _ = g j := ZMod.neg_eq_self_mod_two _
    rw [cycleFiberPrimitive, cycleFiberPrimitive, hval, hprefix]
    rw [Finset.sum_range_zero, add_zero]
end QEC.Coding.FiberBundle
