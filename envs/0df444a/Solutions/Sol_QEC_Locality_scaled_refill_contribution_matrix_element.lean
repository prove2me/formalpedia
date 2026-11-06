-- Prove2me | solution 1 for QEC.Locality.scaled_refill_contribution_matrix_element
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:48:59.272203+00:00
-- url     : https://prove2.me/submissions/7fb89261-fb32-49d3-9008-e7f84c1d1f8d

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_refill_contribution_matrix_element
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
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
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
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
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι)
    (c : Complex) (r : Qubit.Bitstring S.SelectedCoordinates)
    (B : Operator S.complementSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      (((c • tensorLeft S.selectedSystem S.complementSystem (ket r)).comp
        (B.comp (LinearMap.adjoint
          (c • tensorLeft S.selectedSystem S.complementSystem (ket r)))))
        (ket a ⊗ₜ[Complex] k)) =
      (star c * c) * inner Complex (ket b) (ket r) * inner Complex (ket r) (ket a) *
        inner Complex l (B k) := by
  have hadjoint : LinearMap.adjoint
      (c • tensorLeft S.selectedSystem S.complementSystem (ket r)) =
      star c • LinearMap.adjoint
        (tensorLeft S.selectedSystem S.complementSystem (ket r)) := by
    exact map_smulₛₗ LinearMap.adjoint c
      (tensorLeft S.selectedSystem S.complementSystem (ket r))
  rw [hadjoint]
  change inner Complex (ket b ⊗ₜ[Complex] l)
    (c • tensorLeft S.selectedSystem S.complementSystem (ket r)
      (B (star c • (LinearMap.adjoint
        (tensorLeft S.selectedSystem S.complementSystem (ket r)))
        (ket a ⊗ₜ[Complex] k)))) = _
  rw [map_smul, map_smul, smul_smul, inner_smul_right]
  change (c * star c) * _ = _
  rw [mul_comm c (star c)]
  have hmatrix := refill_contribution_matrix_element S r B a b k l
  simpa only [LinearMap.comp_apply, mul_assoc] using
    congrArg (fun z : Complex => (star c * c) * z) hmatrix
end QEC.Locality
