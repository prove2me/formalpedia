-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_cleanedOutside_regionUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:00:57.1863+00:00
-- url     : https://prove2.me/submissions/cb1ea41d-35d6-491f-a355-4bb3130a71ad

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_length_alternatingWidths
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_sum_alternatingWidths
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openVerticalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_periodicVerticalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_nil
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_singleton
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_cons_cons
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_nil
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_singleton
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_cons_cons
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_regionUnion_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_disjoint_support_of_generatedByMeeting_of_noSharedGenerator
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_noSharedGenerator_regionUnion
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PauliSymplectic_support_binaryMul_subset
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_stabilizerCleaningDichotomy
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
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
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
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


attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.length_alternatingWidths
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.sum_alternatingWidths
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openVerticalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_periodicVerticalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_nil
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_singleton
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_cons_cons
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_nil
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_singleton
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_cons_cons
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_regionUnion_iff

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (regions : List (Finset ι))
    (hpairwise : regions.Pairwise H.NoSharedGenerator)
    (hNoLocal : ∀ R ∈ regions, H.NoLocalLogical R)
    (P : Binary ι) (hP : H.code.1.InBinaryNormalizer P) :
    ∃ S : Binary ι,
      S ∈ H.code.1.generatedGroup ∧
      H.code.1.InBinaryNormalizer (binaryMul P S) ∧
      support (binaryMul P S) ⊆ (regionUnion regions)ᶜ := by
  induction regions generalizing P with
  | nil =>
      refine ⟨binaryOne, ?_, ?_, ?_⟩
      · rw [← H.generated_eq]
        exact GeneratedStabilizer.one
      · simpa using hP
      · simp [regionUnion]
  | cons R regions ih =>
      have hpairTail : regions.Pairwise H.NoSharedGenerator := hpairwise.tail
      have hNoLocalTail : ∀ T ∈ regions, H.NoLocalLogical T := by
        intro T hT
        exact hNoLocal T (by simp [hT])
      obtain ⟨S₀, hS₀, hP₀, hOutsideTail⟩ :=
        ih hpairTail hNoLocalTail P hP
      have hNoLocalR : H.NoLocalLogical R :=
        hNoLocal R (by simp)
      have hCleanR :
          ∃ S₁ : Binary ι,
            H.GeneratedByMeeting R S₁ ∧
            S₁ ∈ H.code.1.generatedGroup ∧
            H.code.1.InBinaryNormalizer
              (binaryMul (binaryMul P S₀) S₁) ∧
            support (binaryMul (binaryMul P S₀) S₁) ⊆ Rᶜ := by
        rcases H.stabilizerCleaningDichotomy R with hlocal | hclean
        · exact (hNoLocalR hlocal).elim
        · exact hclean (binaryMul P S₀) hP₀
      obtain ⟨S₁, hS₁Meeting, hS₁, hP₁, hOutsideR⟩ := hCleanR
      have hSeparatedTail :
          H.NoSharedGenerator R (regionUnion regions) :=
        H.noSharedGenerator_regionUnion R regions
          (List.pairwise_cons.mp hpairwise).1
      have hS₁Disjoint :
          Disjoint (support S₁) (regionUnion regions) :=
        H.disjoint_support_of_generatedByMeeting_of_noSharedGenerator
          R (regionUnion regions) S₁ hSeparatedTail hS₁Meeting
      have hOutsideTailAfter :
          support (binaryMul (binaryMul P S₀) S₁) ⊆
            (regionUnion regions)ᶜ := by
        intro i hi
        apply Finset.mem_compl.mpr
        intro hiUnion
        rcases Finset.mem_union.mp
            (support_binaryMul_subset (binaryMul P S₀) S₁ hi) with hiP₀ | hiS₁
        · exact (Finset.mem_compl.mp (hOutsideTail hiP₀)) hiUnion
        · exact (Finset.disjoint_left.mp hS₁Disjoint hiS₁ hiUnion)
      refine ⟨binaryMul S₀ S₁, ?_, ?_, ?_⟩
      · rw [← H.generated_eq] at hS₀ hS₁ ⊢
        exact GeneratedStabilizer.mul hS₀ hS₁
      · simpa [binaryMul_assoc] using hP₁
      · intro i hi
        have hi' :
            i ∈ support (binaryMul (binaryMul P S₀) S₁) := by
          simpa [binaryMul_assoc] using hi
        apply Finset.mem_compl.mpr
        intro hiUnion
        rcases Finset.mem_union.mp hiUnion with hiR | hiTail
        · exact (Finset.mem_compl.mp (hOutsideR hi')) hiR
        · exact (Finset.mem_compl.mp (hOutsideTailAfter hi')) hiTail
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
