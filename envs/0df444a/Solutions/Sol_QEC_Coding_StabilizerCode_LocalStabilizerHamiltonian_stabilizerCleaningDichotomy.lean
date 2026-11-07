-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.stabilizerCleaningDichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:57:33.408238+00:00
-- url     : https://prove2.me/submissions/aa223a64-6db8-4a1a-b0da-ad6f1accd9b9

import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatedVectorSubspace_eq_span_generators
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatedByMeeting_mem_generatedGroup
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_meetingGeneratorSubspace_iff_exists_generatedByMeeting
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_vector_mem_coordinateSubspace_of_support_subset
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_isAlt
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_nondegenerate
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_generatedVectorSubspace_eq_span_generators
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_generatedVectorSubspace_isotropic
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_generatedVectorSubspace_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_orthogonal_iff_inBinaryNormalizer
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_orthogonal_coordinateSubspace
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
import Theorems.Thm_QEC_Locality_support_subset_of_vector_mem_coordinateSubspace
import Theorems.Thm_QEC_Locality_symplecticForm_add_left
import Theorems.Thm_QEC_Locality_symplectic_orthogonal_sup_eq_inf
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_smul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
attribute [local simp] QEC.Locality.centeredRectangleClippedGrowthRadius_zero
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
attribute [local simp] QEC.Locality.mem_longInteractionEndpointQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
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
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) :
    (∃ P : Binary ι,
      H.code.1.InBinaryNormalizer P ∧
      ¬ H.code.1.InGeneratedGroupUpToSign P ∧
      support P ⊆ R) ∨
    (∀ P : Binary ι, H.code.1.InBinaryNormalizer P →
      ∃ S : Binary ι,
        H.GeneratedByMeeting R S ∧
        S ∈ H.code.1.generatedGroup ∧
        H.code.1.InBinaryNormalizer (binaryMul P S) ∧
        support (binaryMul P S) ⊆ Rᶜ) := by
  classical
  by_cases hlocal :
      ∃ P : Binary ι,
        H.code.1.InBinaryNormalizer P ∧
        ¬ H.code.1.InGeneratedGroupUpToSign P ∧
        support P ⊆ R
  · exact Or.inl hlocal
  · right
    let L := H.code.1.generatedVectorSubspace
    let N := FiniteSymplectic.form.orthogonal L
    let W := Locality.coordinateSubspace R
    let A := H.meetingGeneratorSubspace R
    have hNoLocal : N ⊓ W ≤ L := by
      rintro vector ⟨hN, hW⟩
      let E : Binary ι := { phase := 0, vector := vector }
      have hNormalizer : H.code.1.InBinaryNormalizer E := by
        apply (H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer E).1
        simpa [N, L, E] using hN
      have hSupport : support E ⊆ R :=
        Locality.support_subset_of_vector_mem_coordinateSubspace R E
          (by simpa [W, E] using hW)
      by_contra hnotL
      apply hlocal
      refine ⟨E, hNormalizer, ?_, hSupport⟩
      intro hGenerated
      exact hnotL ((H.code.1.vector_mem_generatedVectorSubspace_iff E).2
        hGenerated)
    have hOrthogonalSubset :
        FiniteSymplectic.form.orthogonal
            (A ⊔ FiniteSymplectic.form.orthogonal W) ≤ L := by
      rw [Locality.symplectic_orthogonal_sup_eq_inf,
        LinearMap.BilinForm.orthogonal_orthogonal
          FiniteSymplectic.form_nondegenerate
          FiniteSymplectic.form_isAlt.isRefl]
      rintro vector ⟨hAOrthogonal, hW⟩
      apply hNoLocal
      refine ⟨?_, hW⟩
      change vector ∈
        FiniteSymplectic.form.orthogonal
          H.code.1.generatedVectorSubspace
      rw [H.generatedVectorSubspace_eq_span_generators]
      intro stabilizerVector hStabilizer
      induction hStabilizer using Submodule.span_induction with
      | mem generatorVector hGenerator =>
          rcases hGenerator with ⟨j, rfl⟩
          by_cases hj : H.GeneratorMeets R j
          · exact hAOrthogonal (H.generators j).vector
              (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
          · have hdisjoint : Disjoint (H.generatorSupport j) R := by
              simpa [GeneratorMeets] using hj
            have hsupport : support (H.generators j) ⊆ Rᶜ := by
              intro i hi
              exact Finset.mem_compl.mpr fun hiR =>
                (Finset.disjoint_left.mp hdisjoint hi hiR)
            have hgeneratorWOrthogonal :
                (H.generators j).vector ∈
                  FiniteSymplectic.form.orthogonal W := by
              change (H.generators j).vector ∈
                FiniteSymplectic.form.orthogonal
                  (Locality.coordinateSubspace R)
              rw [Locality.orthogonal_coordinateSubspace]
              exact vector_mem_coordinateSubspace_of_support_subset
                Rᶜ (H.generators j) hsupport
            exact
              FiniteSymplectic.form_isAlt.isRefl.eq_iff.mp
                (hgeneratorWOrthogonal vector hW)
      | zero =>
          change symplecticForm 0 vector = 0
          simp [symplecticForm]
      | add x y _ _ ihx ihy =>
          change symplecticForm (x + y) vector = 0
          change symplecticForm x vector = 0 at ihx
          change symplecticForm y vector = 0 at ihy
          rw [Locality.symplecticForm_add_left, ihx, ihy, add_zero]
      | smul c x _ ihx =>
          change symplecticForm x vector = 0 at ihx
          change symplecticForm (c • x) vector = 0
          by_cases hc : c = 0
          · subst c
            rw [zero_smul]
            change (FiniteSymplectic.form 0) vector = 0
            rw [map_zero]
            rfl
          · have hc1 : c = 1 := zmod_two_eq_one_of_ne_zero hc
            subst c
            simpa using ihx
    have hClean : N ≤ A ⊔ FiniteSymplectic.form.orthogonal W := by
      have hReverse :=
        LinearMap.BilinForm.orthogonal_le
          (B := FiniteSymplectic.form) hOrthogonalSubset
      rw [LinearMap.BilinForm.orthogonal_orthogonal
          FiniteSymplectic.form_nondegenerate
          FiniteSymplectic.form_isAlt.isRefl] at hReverse
      simpa [N, L] using hReverse
    intro P hP
    have hPVector : P.vector ∈ N := by
      simpa [N, L] using
        (H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer P).2 hP
    rcases Submodule.mem_sup.mp (hClean hPVector) with
      ⟨meetingVector, hMeeting, outsideVector, hOutside, hsum⟩
    obtain ⟨S, hSMeeting, hSVector⟩ :=
      (H.mem_meetingGeneratorSubspace_iff_exists_generatedByMeeting
        R meetingVector).1 hMeeting
    have hSGlobal := H.generatedByMeeting_mem_generatedGroup R S hSMeeting
    have hCleanVector :
        (binaryMul P S).vector = outsideVector := by
      change P.vector + S.vector = outsideVector
      rw [hSVector, ← hsum]
      have haddSelf (vector : SymplecticVector (ZMod 2) ι) :
          vector + vector = 0 := by
        calc
          vector + vector = (2 : ZMod 2) • vector := by
            rw [two_smul]
          _ = 0 := by
            have htwo : (2 : ZMod 2) = 0 := by decide
            rw [htwo, zero_smul]
      calc
        meetingVector + outsideVector + meetingVector =
            (meetingVector + meetingVector) + outsideVector := by abel
        _ = 0 + outsideVector := by rw [haddSelf]
        _ = outsideVector := zero_add _
    have hCleanNormalizer :
        H.code.1.InBinaryNormalizer (binaryMul P S) := by
      apply (H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer _).1
      change P.vector + S.vector ∈
        FiniteSymplectic.form.orthogonal
          H.code.1.generatedVectorSubspace
      exact Submodule.add_mem _
        (by simpa [N, L] using hPVector)
        (H.code.1.generatedVectorSubspace_isotropic
          ((H.code.1.vector_mem_generatedVectorSubspace_iff S).2
            ⟨S, hSGlobal, rfl⟩))
    refine ⟨S, hSMeeting, hSGlobal, hCleanNormalizer, ?_⟩
    apply Locality.support_subset_of_vector_mem_coordinateSubspace Rᶜ
      (binaryMul P S)
    rw [hCleanVector]
    simpa [W, Locality.orthogonal_coordinateSubspace] using hOutside
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
