-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.GVPlus.mem_dual_systematicCode_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:48:30.068799+00:00
-- url     : https://prove2.me/submissions/48ba610e-118f-44d8-a7b7-94caf6a0acb6

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.PowersetCard
import Mathlib.FieldTheory.Finiteness
import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_wordPairing_systematicDualEncode_systematicEncode
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.BalancedProduct.GVPlus
open Classical
namespace QEC.Coding.BalancedProduct.GVPlus
theorem _root_.solution {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2))
    (x : Sum (Fin k) (Fin r) → ZMod 2) :
    x ∈ (systematicCode A).dual.carrier ↔
      ∃ y : Fin r → ZMod 2, systematicDualEncode A y = x := by
  constructor
  · intro hx
    let y : Fin r → ZMod 2 := fun j => x (Sum.inr j)
    refine ⟨y, ?_⟩
    funext q
    cases q with
    | inr j => rfl
    | inl i =>
        have horth := (systematicCode A).orthogonal_of_mem_dual hx
          (show systematicEncode A (Pi.single i 1) ∈
              (systematicCode A).carrier from
            (mem_systematicCode A _).2 ⟨Pi.single i 1, rfl⟩)
        simp only [wordPairing_apply, dotProduct, Fintype.sum_sum_type,
          systematicEncode] at horth
        have hleft : (∑ i', x (Sum.inl i') *
            (Pi.single i (1 : ZMod 2) : Fin k → ZMod 2) i') =
            x (Sum.inl i) := by
          rw [Fintype.sum_eq_single i]
          · simp
          · intro i' hi'
            simp [Pi.single_eq_of_ne hi']
        rw [hleft] at horth
        have hright :
            (∑ j, x (Sum.inr j) * Matrix.vecMul (Pi.single i 1) A j) =
              Matrix.mulVec A y i := by
          have hbasis (j : Fin r) :
              Matrix.vecMul
                  (Pi.single i (1 : ZMod 2) : Fin k → ZMod 2) A j = A i j := by
            rw [Matrix.vecMul, dotProduct, Fintype.sum_eq_single i]
            · simp
            · intro i' hi'
              simp [Pi.single_eq_of_ne hi']
          simp_rw [hbasis]
          simp [Matrix.mulVec, dotProduct, y, mul_comm]
        rw [hright] at horth
        exact (eq_neg_of_add_eq_zero_left horth).symm
  · rintro ⟨y, rfl⟩
    refine ((systematicCode A).mem_dual _).2 ?_
    intro c hc
    rcases (mem_systematicCode A c).1 hc with ⟨m, rfl⟩
    exact wordPairing_systematicDualEncode_systematicEncode A y m
end QEC.Coding.BalancedProduct.GVPlus
