-- Prove2me | solution 1 for QEC.Locality.wordPauli_phase_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:46:51.306199+00:00
-- url     : https://prove2.me/submissions/34fa7669-9438-4ec0-9db8-099c60184d01

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_word_add_self_zero
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
theorem _root_.solution {α : Type u} [Fintype α] [DecidableEq α]
    (x z : Coding.Word (ZMod 2) α) (a b : Qubit.Bitstring α) :
    star (Qubit.zSupportPhase (PauliSymplectic.binarySupport z)
      (Qubit.flipSupport (PauliSymplectic.binarySupport x) b)) *
      Qubit.zSupportPhase (PauliSymplectic.binarySupport z)
        (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) =
      PauliSymplectic.binaryPhaseScalar
        (Coding.wordPairing (F := ZMod 2) (ι := α) z
          ((PauliSymplectic.bitstringWordEquiv α b) +
            PauliSymplectic.bitstringWordEquiv α a)) := by
  rw [PauliSymplectic.zSupportPhase_eq_binaryPhaseScalar_wordPairing,
    PauliSymplectic.zSupportPhase_eq_binaryPhaseScalar_wordPairing,
    PauliSymplectic.binaryPhaseScalar_star, ← PauliSymplectic.binaryPhaseScalar_add]
  congr 1
  rw [← (Coding.wordPairing (F := ZMod 2) (ι := α) z).map_add]
  rw [PauliSymplectic.bitstringWordEquiv_flipSupport,
    PauliSymplectic.bitstringWordEquiv_flipSupport]
  have hx : x + x = 0 := word_add_self_zero x
  calc
    (Coding.wordPairing (F := ZMod 2) (ι := α) z)
        ((PauliSymplectic.bitstringWordEquiv α b) + x +
          ((PauliSymplectic.bitstringWordEquiv α a) + x)) =
      (Coding.wordPairing (F := ZMod 2) (ι := α) z)
        ((PauliSymplectic.bitstringWordEquiv α b +
          PauliSymplectic.bitstringWordEquiv α a) + (x + x)) := by
        congr 1
        abel
    _ = _ := by simp [hx]
end QEC.Locality
