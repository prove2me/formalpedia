-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.mem_couniqueNeighbors_iff_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:53:51.521477+00:00
-- url     : https://prove2.me/submissions/86a2a3aa-15d9-4302-838d-ec2bf289ff6d

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
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
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) (b : Fin (4 * r)) :
    b ∈ couniqueNeighbors sample S ↔
      ∃ a ∈ S,
        sample (a, b) = true ∧
          ∀ a' ∈ S, sample (a', b) = true → a' = a := by
  constructor
  · intro hb
    have hcard :
        (S.filter fun a => sample (a, b)).card = 1 := by
      exact (Finset.mem_filter.mp hb).2
    rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
    have haMem : a ∈ S.filter fun a => sample (a, b) := by
      rw [ha]
      simp
    refine ⟨a, (Finset.mem_filter.mp haMem).1,
      (Finset.mem_filter.mp haMem).2, ?_⟩
    intro a' ha'S ha'Edge
    have ha'Mem : a' ∈ S.filter fun a => sample (a, b) :=
      Finset.mem_filter.mpr ⟨ha'S, ha'Edge⟩
    rw [ha] at ha'Mem
    simpa using ha'Mem
  · rintro ⟨a, haS, haEdge, haUnique⟩
    have hfilter :
        S.filter (fun a' => sample (a', b)) = {a} := by
      ext a'
      constructor
      · intro ha'
        have ha'S := (Finset.mem_filter.mp ha').1
        have ha'Edge := (Finset.mem_filter.mp ha').2
        simp [haUnique a' ha'S ha'Edge]
      · intro ha'
        have ha'eq : a' = a := by simpa using ha'
        subst a'
        exact Finset.mem_filter.mpr ⟨haS, haEdge⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (S.filter fun a' => sample (a', b)).card = 1
    rw [hfilter, Finset.card_singleton]
end QEC.Coding.FiberBundle.RandomBase
