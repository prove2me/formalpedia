-- Prove2me | solution 1 for QEC.QLDPC.chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:41.249362+00:00
-- url     : https://prove2.me/submissions/41521179-bbb1-420e-9dfd-4468cfc0270b

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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


attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
section
namespace QEC
universe u v w x
open scoped Classical
namespace Coding.ChainComplexData
end Coding.ChainComplexData
namespace Coding.StabilizerCode
open PauliSymplectic
end Coding.StabilizerCode
namespace QLDPC
namespace CheckIncidence
variable {χ ι : Type*} [Fintype χ] [Fintype ι]
end CheckIncidence
private theorem wordLinearMapTranspose_single_apply
    {F : Type u} {I K : Type v} [Field F] [Fintype F]
    [Fintype I] [Fintype K]
    (A : Coding.Word F I →ₗ[F] Coding.Word F K) (k : K) (q : I) :
    Coding.wordLinearMapTranspose A
        (Coding.canonicalBasisWord (F := F) k) q =
      A (Coding.canonicalBasisWord (F := F) q) k := by
  classical
  unfold Coding.wordLinearMapTranspose Coding.canonicalBasisWord
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro k' hne
    simp [hne]
end QLDPC
end QEC
end

set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC
namespace QEC.QLDPC
theorem _root_.solution
    {F : Type u} {I K L : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [Fintype K] [Fintype L]
    (C : Coding.ChainComplexData F (Coding.Word F K) (Coding.Word F I)
      (Coding.Word F L)) (q : I) :
    ((chainComplexBoundaryIncidence C).variableSupport q).card =
      Coding.HammingWeight
        (C.boundary1 (Coding.canonicalBasisWord (F := F) q)) +
      Coding.HammingWeight
        (Coding.wordLinearMapTranspose C.boundary2
          (Coding.canonicalBasisWord (F := F) q)) := by
  classical
  let x := C.boundary1 (Coding.canonicalBasisWord (F := F) q)
  let z := Coding.wordLinearMapTranspose C.boundary2
    (Coding.canonicalBasisWord (F := F) q)
  have hSupport :
      (chainComplexBoundaryIncidence C).variableSupport q =
        Coding.hammingSupport (Sum.elim x z) := by
    ext c
    rw [CheckIncidence.mem_variableSupport]
    simp only [Coding.hammingSupport, Finset.mem_filter, Finset.mem_univ,
      true_and]
    cases c with
    | inl k =>
        dsimp [chainComplexBoundaryIncidence, x]
        rw [wordLinearMapTranspose_single_apply]
    | inr l =>
        dsimp [chainComplexBoundaryIncidence, z]
        rw [wordLinearMapTranspose_single_apply]
  rw [hSupport]
  change Coding.HammingWeight (Sum.elim x z) =
    Coding.HammingWeight x + Coding.HammingWeight z
  classical
  let e :
      {s : Sum K L // Sum.elim x z s ≠ 0} ≃
        Sum {k : K // x k ≠ 0} {l : L // z l ≠ 0} :=
    { toFun := fun s =>
        match s with
        | ⟨Sum.inl k, hk⟩ => Sum.inl ⟨k, hk⟩
        | ⟨Sum.inr l, hl⟩ => Sum.inr ⟨l, hl⟩
      invFun := fun s =>
        match s with
        | Sum.inl k => ⟨Sum.inl k.1, k.2⟩
        | Sum.inr l => ⟨Sum.inr l.1, l.2⟩
      left_inv := by rintro ⟨k | l, h⟩ <;> rfl
      right_inv := by rintro (k | l) <;> rfl }
  calc
    Coding.HammingWeight (Sum.elim x z) =
        Fintype.card {s : Sum K L // Sum.elim x z s ≠ 0} := by
      simp [Coding.HammingWeight, Coding.hammingSupport,
        Fintype.card_subtype]
    _ = Fintype.card (Sum {k : K // x k ≠ 0} {l : L // z l ≠ 0}) :=
      Fintype.card_congr e
    _ = Coding.HammingWeight x + Coding.HammingWeight z := by
      simp [Coding.HammingWeight, Coding.hammingSupport,
        Fintype.card_subtype]
end QEC.QLDPC
