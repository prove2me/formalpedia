-- Prove2me | solution 1 for QEC.Locality.semanticStabilizerDistance_erasureRecoverableFromRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:12:26.39821+00:00
-- url     : https://prove2.me/submissions/8ecabdfb-e8e1-4b48-a700-962c05a94d80

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Theorems.Thm_QEC_Locality_embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl
import Theorems.Thm_QEC_Locality_semanticStabilizerDistance_localPauli_pairProductCriterion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
import Theorems.Thm_QEC_Locality_erasureRecoverableFromRegister_of_localPauliTwirl_correctable
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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
open QEC Semantics Coding
open scoped TensorProduct
open PauliSymplectic
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (Q : StabilizerCode.SourceValidBinary ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q d)
    (S : FiniteSubsystem ι) (hSelected : S.selected.card < d) :
    ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) S.complementSystem Q.1.code
        S.erasureChannelFromRegister recovery := by
  have hPairs : ∀ p q : LocalPauliWordIndex S,
      localPauliAmplitude S ≠ 0 → localPauliAmplitude S ≠ 0 →
        Q.1.InGeneratedGroupUpToSign
            (binaryMul (binaryDagger (embeddedLocalPauli S p))
              (embeddedLocalPauli S q)) ∨
          ¬ Q.1.InBinaryNormalizer
            (binaryMul (binaryDagger (embeddedLocalPauli S p))
              (embeddedLocalPauli S q)) := by
    intro p q _ _
    exact semanticStabilizerDistance_localPauli_pairProductCriterion
      Q d hDistance S hSelected p q
  rcases
      (StabilizerCode.exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
        Q (embeddedLocalPauli S) (fun _ => localPauliAmplitude S)
        (embeddedLocalPauliKrausFamily_complete S)).2 hPairs with
    ⟨twirlRecovery, hTwirlKrausRecovery⟩
  rcases
      (Semantics.exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
        Q.1.code
        (binaryPauliKrausFamily (embeddedLocalPauli S)
          (fun _ => localPauliAmplitude S))).1
        ⟨twirlRecovery, hTwirlKrausRecovery⟩ with
    ⟨hComplete, twirlRecovery, hTwirlRecovery⟩
  have hTwirlRecovery' : Correctable (Qubit.QubitRegister ι)
      (Qubit.QubitRegister ι) Q.1.code
      ((binaryPauliKrausFamily (embeddedLocalPauli S)
        (fun _ => localPauliAmplitude S)).toQuantumChannel
          (embeddedLocalPauliKrausFamily_complete S)) twirlRecovery := by
    simpa using hTwirlRecovery
  have hLocalTwirlRecovery : Correctable (Qubit.QubitRegister ι)
      (Qubit.QubitRegister ι) Q.1.code (localPauliTwirl S) twirlRecovery := by
    rw [← embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl]
    exact hTwirlRecovery'
  exact erasureRecoverableFromRegister_of_localPauliTwirl_correctable
    S Q.1.code twirlRecovery hLocalTwirlRecovery
end QEC.Locality
