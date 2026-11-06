-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_of_fixedGeneratorDecoupled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:21:11.671164+00:00
-- url     : https://prove2.me/submissions/24b07878-dd6b-4425-a29c-ad8de35485bc

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Theorems.Thm_QEC_Locality_restrictBinaryTo_vector_add_of_support_subset_union
import Theorems.Thm_QEC_Locality_inBinaryNormalizer_restrictBinaryTo_of_no_cross_edge
import Theorems.Thm_QEC_Locality_inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_generatedVectorSubspace_iff
import Theorems.Thm_QEC_Locality_embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl
import Theorems.Thm_QEC_Locality_erasureRecoverableFromRegister_of_localPauliTwirl_correctable
import Theorems.Thm_QEC_Locality_support_relative_embeddedLocalPauli_subset
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
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B : FiniteSubsystem ι)
    (recoveryA : QuantumChannel A.complementSystem (Qubit.QubitRegister ι))
    (recoveryB : QuantumChannel B.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryA : Correctable (Qubit.QubitRegister ι) A.complementSystem P.semanticCode
      A.erasureChannelFromRegister recoveryA)
    (hRecoveryB : Correctable (Qubit.QubitRegister ι) B.complementSystem P.semanticCode
      B.erasureChannelFromRegister recoveryB)
    (hDecoupled : P.fixedGeneratorDecoupled (A.selected : Set ι) (B.selected : Set ι)) :
    ∃ recovery : QuantumChannel (unionSubsystem A B).complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (unionSubsystem A B).complementSystem P.semanticCode
        (unionSubsystem A B).erasureChannelFromRegister recovery := by
  have hAB : Disjoint A.selected B.selected := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact (Set.disjoint_left.mp hDecoupled.1) (by simpa using hiA) (by simpa using hiB)
  let U := unionSubsystem A B
  have hPairs : ∀ p q : LocalPauliWordIndex U,
      localPauliAmplitude U ≠ 0 → localPauliAmplitude U ≠ 0 →
        P.code.1.InGeneratedGroupUpToSign
            (binaryMul (binaryDagger (embeddedLocalPauli U p))
              (embeddedLocalPauli U q)) ∨
          ¬ P.code.1.InBinaryNormalizer
            (binaryMul (binaryDagger (embeddedLocalPauli U p))
              (embeddedLocalPauli U q)) := by
    intro p q _ _
    let E := binaryMul (binaryDagger (embeddedLocalPauli U p))
      (embeddedLocalPauli U q)
    by_cases hNormalizer : P.code.1.InBinaryNormalizer E
    · left
      have hSupport : support E ⊆ A.selected ∪ B.selected := by
        simpa [E, U, unionSubsystem] using support_relative_embeddedLocalPauli_subset U p q
      have hDecompose := restrictBinaryTo_vector_add_of_support_subset_union
        A.selected B.selected E hAB hSupport
      obtain ⟨hNormalizerA, hNormalizerB⟩ :=
        inBinaryNormalizer_restrictBinaryTo_of_no_cross_edge P A.selected B.selected E
          hAB hDecoupled.2 hDecompose hNormalizer
      have hGeneratedA :=
        inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
          P A recoveryA hRecoveryA E hNormalizerA
      have hGeneratedB :=
        inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
          P B recoveryB hRecoveryB E hNormalizerB
      apply (StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 E).1
      rw [hDecompose]
      exact P.code.1.generatedVectorSubspace.add_mem
        ((StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).2 hGeneratedA)
        ((StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).2 hGeneratedB)
    · exact Or.inr hNormalizer
  rcases
      (StabilizerCode.exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
        P.code (embeddedLocalPauli U) (fun _ => localPauliAmplitude U)
        (embeddedLocalPauliKrausFamily_complete U)).2 hPairs with
    ⟨twirlRecovery, hTwirlKrausRecovery⟩
  rcases
      (Semantics.exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
        P.semanticCode
        (binaryPauliKrausFamily (embeddedLocalPauli U)
          (fun _ => localPauliAmplitude U))).1
        ⟨twirlRecovery, hTwirlKrausRecovery⟩ with
    ⟨_hComplete, twirlRecovery, hTwirlRecovery⟩
  have hTwirlRecovery' : Correctable (Qubit.QubitRegister ι)
      (Qubit.QubitRegister ι) P.semanticCode
      ((binaryPauliKrausFamily (embeddedLocalPauli U)
        (fun _ => localPauliAmplitude U)).toQuantumChannel
          (embeddedLocalPauliKrausFamily_complete U)) twirlRecovery := by
    simpa using hTwirlRecovery
  have hLocalTwirlRecovery : Correctable (Qubit.QubitRegister ι)
      (Qubit.QubitRegister ι) P.semanticCode (localPauliTwirl U) twirlRecovery := by
    rw [← embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl]
    exact hTwirlRecovery'
  exact erasureRecoverableFromRegister_of_localPauliTwirl_correctable
    U P.semanticCode twirlRecovery hLocalTwirlRecovery
end QEC.Locality
