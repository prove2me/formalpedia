-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.exists_bkTwoPassDimensionBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:12:13.36679+00:00
-- url     : https://prove2.me/submissions/271f1395-d079-413b-86d5-92579945ec1f

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_TwoPassDimension
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_bkRecursivePartition_erasureRecoverable
import Theorems.Thm_QEC_Locality_BKRecursivePartition_remainder_card_le_bkSumPreservingRecurrence
import Theorems.Thm_QEC_Locality_BKRecursivePartition_remainder_recurrence_le_bkSumPreservingRecurrenceTwice
import Theorems.Thm_QEC_Locality_exists_bkRecursivePartition
import Theorems.Thm_QEC_Locality_two_correctable_regions_encodedQubits_le_separator_card
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
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
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open QEC Semantics Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : SemanticStabilizerDistance P.code d) (hd : 0 < d) :
    ∃ first : BKRecursivePartition P.fixedGeneratorInteractionGraph d Finset.univ,
      ∃ second : BKRecursivePartition P.fixedGeneratorInteractionGraph d first.remainder,
        let A := bkPartitionRegion first
        let B := bkPartitionRegion second
        let C : FiniteSubsystem ι := ⟨second.remainder⟩
        Disjoint A.selected B.selected ∧
          Disjoint A.selected C.selected ∧
          Disjoint B.selected C.selected ∧
          A.selected ∪ B.selected ∪ C.selected = Finset.univ ∧
          ∃ recoveryA : QuantumChannel A.complementSystem (Qubit.QubitRegister ι),
            Correctable (Qubit.QubitRegister ι) A.complementSystem P.semanticCode
                A.erasureChannelFromRegister recoveryA ∧
              ∃ recoveryB : QuantumChannel B.complementSystem (Qubit.QubitRegister ι),
                Correctable (Qubit.QubitRegister ι) B.complementSystem P.semanticCode
                    B.erasureChannelFromRegister recoveryB ∧
                  P.encodedQubits ≤ C.selected.card ∧
                  first.remainder.card ≤ bkSumPreservingRecurrence
                    P.fixedGeneratorInteractionGraph d (Fintype.card ι) ∧
                  C.selected.card ≤ bkSeparatorRecurrence
                    P.fixedGeneratorInteractionGraph d first.remainder ∧
                  C.selected.card ≤ bkSumPreservingRecurrenceTwice
                    P.fixedGeneratorInteractionGraph d (Fintype.card ι) := by
  rcases exists_bkRecursivePartition P.fixedGeneratorInteractionGraph d hd Finset.univ with
    ⟨first⟩
  rcases exists_bkRecursivePartition P.fixedGeneratorInteractionGraph d hd first.remainder with
    ⟨second⟩
  let A := bkPartitionRegion first
  let B := bkPartitionRegion second
  let C : FiniteSubsystem ι := ⟨second.remainder⟩
  have hARecovery := P.bkRecursivePartition_erasureRecoverable d hDistance Finset.univ first
  have hBRecovery :=
    P.bkRecursivePartition_erasureRecoverable d hDistance first.remainder second
  rcases hARecovery with ⟨recoveryA, hRecoveryA⟩
  rcases hBRecovery with ⟨recoveryB, hRecoveryB⟩
  have hBSubset : B.selected ⊆ first.remainder := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨piece, hpiece, hxpiece⟩
    exact second.piece_subset piece hpiece hxpiece
  have hCSubset : C.selected ⊆ first.remainder := second.remainder_subset
  have hAB : Disjoint A.selected B.selected := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    exact (Finset.disjoint_left.mp first.pieces_remainder_disjoint) hxA (hBSubset hxB)
  have hAC : Disjoint A.selected C.selected := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxC
    exact (Finset.disjoint_left.mp first.pieces_remainder_disjoint) hxA (hCSubset hxC)
  have hBC : Disjoint B.selected C.selected := second.pieces_remainder_disjoint
  have hCover : A.selected ∪ B.selected ∪ C.selected = Finset.univ := by
    change first.pieces.biUnion id ∪ second.pieces.biUnion id ∪ second.remainder = Finset.univ
    rw [Finset.union_assoc, second.covers, first.covers]
  have hDimension : P.encodedQubits ≤ C.selected.card :=
    two_correctable_regions_encodedQubits_le_separator_card P A B C hAB hAC hBC hCover
      recoveryA hRecoveryA recoveryB hRecoveryB
  have hFirstCharge : first.remainder.card ≤ bkSumPreservingRecurrence
      P.fixedGeneratorInteractionGraph d (Fintype.card ι) := by
    simpa using first.remainder_card_le_bkSumPreservingRecurrence
  have hSecondCharge : second.remainder.card ≤
      bkSeparatorRecurrence P.fixedGeneratorInteractionGraph d first.remainder :=
    second.remainder_card_le
  have hSecondScale : bkSeparatorRecurrence P.fixedGeneratorInteractionGraph d
        first.remainder ≤
      bkSumPreservingRecurrenceTwice P.fixedGeneratorInteractionGraph d
        (Fintype.card ι) := by
    simpa using first.remainder_recurrence_le_bkSumPreservingRecurrenceTwice
  refine ⟨first, second, ?_⟩
  dsimp only
  exact ⟨hAB, hAC, hBC, hCover, recoveryA, hRecoveryA, recoveryB, hRecoveryB,
    hDimension, hFirstCharge, hSecondCharge, hSecondCharge.trans hSecondScale⟩
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
