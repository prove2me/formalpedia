-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:26:18.497325+00:00
-- url     : https://prove2.me/submissions/83bfa47c-a328-4a61-8ed6-5b217e0f7c94

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Theorems.Thm_QEC_Locality_support_restrictBinaryTo_subset
import Theorems.Thm_QEC_Locality_commutes_of_disjoint_support
import Theorems.Thm_QEC_Locality_restrictBinaryTo_vector_add_of_support_subset_union
import Theorems.Thm_QEC_Locality_symplecticForm_add_right
import Theorems.Thm_QEC_Locality_exists_cleanedOutside_of_erasure_correctable
import Theorems.Thm_QEC_Locality_inBinaryNormalizer_restrictBinaryTo_of_no_cross_edge
import Theorems.Thm_QEC_Locality_inGeneratedGroupUpToSign_restrictBinaryTo_of_subset_erasure_correctable
import Theorems.Thm_QEC_Locality_fixedGeneratorNoCrossEdge_sdiff_compl_union_of_outerBoundary_subset
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_localPauli_pair_criterion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_isAlt
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_exists_inBinaryNormalizer_not_commutes
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_generatedVectorSubspace_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_orthogonal_iff_inBinaryNormalizer
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
    (U T : FiniteSubsystem ι)
    (recoveryU : QuantumChannel U.complementSystem (Qubit.QubitRegister ι))
    (recoveryT : QuantumChannel T.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryU : Correctable (Qubit.QubitRegister ι) U.complementSystem P.semanticCode
      U.erasureChannelFromRegister recoveryU)
    (hRecoveryT : Correctable (Qubit.QubitRegister ι) T.complementSystem P.semanticCode
      T.erasureChannelFromRegister recoveryT)
    (hBoundary : P.fixedGeneratorOuterBoundary (U.selected : Set ι) ⊆
      (T.selected : Set ι)) :
    ∃ recovery : QuantumChannel (unionSubsystem U T).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (unionSubsystem U T).complementSystem
        P.semanticCode (unionSubsystem U T).erasureChannelFromRegister recovery := by
  apply exists_erasureRecovery_of_localPauli_pair_criterion P (unionSubsystem U T)
  intro p q _ _
  let E := binaryMul (binaryDagger (embeddedLocalPauli (unionSubsystem U T) p))
    (embeddedLocalPauli (unionSubsystem U T) q)
  by_cases hNormalizer : P.code.1.InBinaryNormalizer E
  · left
    by_contra hNotGenerated
    obtain ⟨F, hFNormalizer, hNotCommutes⟩ :=
      StabilizerCode.exists_inBinaryNormalizer_not_commutes P.code.1
        hNormalizer hNotGenerated
    obtain ⟨sT, hsT, outside, hOutsideNormalizer, hOutsideSupport, hCleanT⟩ :=
      exists_cleanedOutside_of_erasure_correctable
        P T recoveryT hRecoveryT F hFNormalizer
    have hSupportParts : support outside ⊆
        (U.selected \ T.selected) ∪ (U.selected ∪ T.selected)ᶜ := by
      intro i hi
      have hiTCompl := hOutsideSupport hi
      have hiNotT : i ∉ T.selected := Finset.mem_compl.mp hiTCompl
      by_cases hiU : i ∈ U.selected
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hiU, hiNotT⟩)
      · apply Finset.mem_union_right
        exact Finset.mem_compl.mpr (by
          intro hiUnion
          rcases Finset.mem_union.mp hiUnion with hiU' | hiT
          · exact hiU hiU'
          · exact hiNotT hiT)
    have hPartsDisjoint : Disjoint (U.selected \ T.selected)
        (U.selected ∪ T.selected)ᶜ := by
      apply Finset.disjoint_left.mpr
      intro i hiLeft hiRight
      exact (Finset.mem_compl.mp hiRight)
        (Finset.mem_union_left T.selected (Finset.mem_sdiff.mp hiLeft).1)
    have hNoCross :=
      fixedGeneratorNoCrossEdge_sdiff_compl_union_of_outerBoundary_subset
        P U.selected T.selected hBoundary
    have hDecompose : outside.vector =
        (restrictBinaryTo (U.selected \ T.selected) outside).vector +
          (restrictBinaryTo (U.selected ∪ T.selected)ᶜ outside).vector :=
      restrictBinaryTo_vector_add_of_support_subset_union
        (U.selected \ T.selected) (U.selected ∪ T.selected)ᶜ outside
          hPartsDisjoint hSupportParts
    obtain ⟨hNormalizerUOnly, _hNormalizerOutsideUnion⟩ :=
      inBinaryNormalizer_restrictBinaryTo_of_no_cross_edge P
        (U.selected \ T.selected) (U.selected ∪ T.selected)ᶜ outside
        hPartsDisjoint hNoCross hDecompose hOutsideNormalizer
    have hGeneratedUOnly :=
      inGeneratedGroupUpToSign_restrictBinaryTo_of_subset_erasure_correctable
        P U (U.selected \ T.selected) Finset.sdiff_subset
          recoveryU hRecoveryU outside hNormalizerUOnly
    have hEOrthogonal : E.vector ∈
        FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace :=
      (StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer P.code.1 E).2
        hNormalizer
    have hEsT : symplecticForm E.vector sT = 0 := by
      change FiniteSymplectic.form E.vector sT = 0
      exact FiniteSymplectic.form_isAlt.isRefl sT E.vector (hEOrthogonal sT hsT)
    have hUOnlyVector :
        (restrictBinaryTo (U.selected \ T.selected) outside).vector ∈
          P.code.1.generatedVectorSubspace :=
      (StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).2
        hGeneratedUOnly
    have hEUOnly : symplecticForm E.vector
        (restrictBinaryTo (U.selected \ T.selected) outside).vector = 0 := by
      change FiniteSymplectic.form E.vector
        (restrictBinaryTo (U.selected \ T.selected) outside).vector = 0
      exact FiniteSymplectic.form_isAlt.isRefl
        (restrictBinaryTo (U.selected \ T.selected) outside).vector E.vector
          (hEOrthogonal _ hUOnlyVector)
    have hESupport : support E ⊆ U.selected ∪ T.selected := by
      simpa [E, unionSubsystem] using
        support_relative_embeddedLocalPauli_subset (unionSubsystem U T) p q
    have hOutsideUnionSupport :
        support (restrictBinaryTo (U.selected ∪ T.selected)ᶜ outside) ⊆
          (U.selected ∪ T.selected)ᶜ :=
      support_restrictBinaryTo_subset _ _
    have hSupportDisjoint : Disjoint (support E)
        (support (restrictBinaryTo (U.selected ∪ T.selected)ᶜ outside)) := by
      apply Finset.disjoint_left.mpr
      intro i hiE hiOutside
      exact (Finset.mem_compl.mp (hOutsideUnionSupport hiOutside)) (hESupport hiE)
    have hEOutsideUnion : Commutes E
        (restrictBinaryTo (U.selected ∪ T.selected)ᶜ outside) :=
      commutes_of_disjoint_support E _ hSupportDisjoint
    have hCommutesF : Commutes E F := by
      change symplecticForm E.vector F.vector = 0
      rw [hCleanT, symplecticForm_add_right, hDecompose,
        symplecticForm_add_right, hEsT, hEUOnly]
      change 0 + (0 + symplecticForm E.vector
        (restrictBinaryTo (U.selected ∪ T.selected)ᶜ outside).vector) = 0
      simpa [Commutes] using hEOutsideUnion
    exact hNotCommutes hCommutesF
  · exact Or.inr hNormalizer
end QEC.Locality
