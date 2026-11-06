-- Prove2me | solution 1 for QEC.Locality.wordBinaryPauli_apply_ket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:40:03.716922+00:00
-- url     : https://prove2.me/submissions/e4224a55-ff01-4c19-9239-4166669ab25f

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_flipSupport_flipSupport
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
    (p : LocalPauliWordIndex S) (bits : Qubit.Bitstring S.SelectedCoordinates) :
    PauliSymplectic.toQubitOperator (wordBinaryPauli S p) (ket bits) =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2) bits •
        ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) bits) := by
  ext output
  rw [PauliSymplectic.toQubitOperator_apply]
  simp only [wordBinaryPauli, PauliSymplectic.xSupport, PauliSymplectic.zSupport,
    PauliSymplectic.binaryPhaseScalar_zero, one_mul]
  change Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) output) *
      ket bits (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) output) =
    (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2) bits •
      ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) bits)) output
  simp only [ket, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  by_cases h : Qubit.flipSupport (PauliSymplectic.binarySupport p.1) output = bits
  · have h' : output = Qubit.flipSupport (PauliSymplectic.binarySupport p.1) bits := by
      rw [← h]
      exact (flipSupport_flipSupport (α := S.SelectedCoordinates) _ _).symm
    subst output
    simp [flipSupport_flipSupport (α := S.SelectedCoordinates)]
  · have h' : output ≠ Qubit.flipSupport (PauliSymplectic.binarySupport p.1) bits := by
      intro h'
      apply h
      rw [h', flipSupport_flipSupport (α := S.SelectedCoordinates)]
    simp [h, h']
end QEC.Locality
