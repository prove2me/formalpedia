-- Prove2me | solution 1 for QEC.Locality.exists_cleanedOutside_of_erasure_correctable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:23:35.45251+00:00
-- url     : https://prove2.me/submissions/13e9a767-8b7e-4f42-aa8e-552f8f444deb

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Theorems.Thm_QEC_Locality_support_subset_of_vector_mem_coordinateSubspace
import Theorems.Thm_QEC_Locality_symplectic_orthogonal_inf_eq_sup
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_isAlt
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_nondegenerate
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_generatedVectorSubspace_isotropic
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_orthogonal_iff_inBinaryNormalizer
import Theorems.Thm_QEC_Locality_normalizer_inf_coordinateSubspace_le_stabilizer
import Theorems.Thm_QEC_Locality_orthogonal_coordinateSubspace
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
    (S : FiniteSubsystem ι)
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
      S.erasureChannelFromRegister recovery)
    (E : Binary ι) (hNormalizer : P.code.1.InBinaryNormalizer E) :
    ∃ s, s ∈ P.code.1.generatedVectorSubspace ∧
      ∃ outside : Binary ι,
        P.code.1.InBinaryNormalizer outside ∧
        support outside ⊆ S.selectedᶜ ∧
        E.vector = s + outside.vector := by
  let L := P.code.1.generatedVectorSubspace
  let N := FiniteSymplectic.form.orthogonal L
  let W := coordinateSubspace S.selected
  have hLocal : N ⊓ W ≤ L := by
    simpa [L, N, W] using
      normalizer_inf_coordinateSubspace_le_stabilizer P S recovery hRecovery
  have hClean : N ≤ L ⊔ coordinateSubspace S.selectedᶜ := by
    have hOrth : FiniteSymplectic.form.orthogonal L ≤
        FiniteSymplectic.form.orthogonal (N ⊓ W) :=
      LinearMap.BilinForm.orthogonal_le hLocal
    rw [symplectic_orthogonal_inf_eq_sup,
      LinearMap.BilinForm.orthogonal_orthogonal FiniteSymplectic.form_nondegenerate
        FiniteSymplectic.form_isAlt.isRefl,
      orthogonal_coordinateSubspace] at hOrth
    simpa [N, W] using hOrth
  have hEVector : E.vector ∈ N := by
    simpa [N, L] using
      (StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer P.code.1 E).2 hNormalizer
  rcases Submodule.mem_sup.mp (hClean hEVector) with ⟨s, hs, outsideVector, hOutside, hsum⟩
  let outside : Binary ι := { phase := 0, vector := outsideVector }
  have hOutsideNormalizer : P.code.1.InBinaryNormalizer outside := by
    apply (StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer P.code.1 outside).1
    have hsNormalizer : s ∈ N := by
      exact P.code.1.generatedVectorSubspace_isotropic hs
    have hsumNormalizer : s + outsideVector ∈ N := by
      rw [hsum]
      exact hEVector
    have houtside : outsideVector ∈ N := by
      simpa only [add_sub_cancel_left] using N.sub_mem hsumNormalizer hsNormalizer
    exact houtside
  refine ⟨s, hs, outside, hOutsideNormalizer, ?_, ?_⟩
  · exact support_subset_of_vector_mem_coordinateSubspace S.selectedᶜ outside (by
      simpa [outside] using hOutside)
  · simpa [outside] using hsum.symm
end QEC.Locality
