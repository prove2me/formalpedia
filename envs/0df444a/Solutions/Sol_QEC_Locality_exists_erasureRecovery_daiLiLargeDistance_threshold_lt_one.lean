-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_daiLiLargeDistance_threshold_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:28:15.564972+00:00
-- url     : https://prove2.me/submissions/4d21ed50-e831-4097-8dda-74deb854bf46

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Theorems.Thm_QEC_Locality_card_longInteractionEndpointQubits_lt_distance
import Theorems.Thm_QEC_Locality_no_fixedGeneratorInteraction_from_outside_longEndpoints_of_threshold_lt_one
import Theorems.Thm_QEC_Locality_daiLiSingletonsOutsideLongEndpoints_fixedGeneratorDecoupled
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorDecoupled_iff_disjoint_no_cross_interaction
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_adj_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_symmetric
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_fixedGeneratorDecoupled
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_semanticStabilizerDistance_erasureRecoverableFromRegister
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
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
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
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d)
    (hdTwo : 2 ≤ d)
    (hThreshold : daiLiLargeDistanceThreshold d (Fintype.card ι) < 1) :
    ∃ recovery : QuantumChannel
        (daiLiFiniteSubsystem (Finset.univ : Finset ι)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiFiniteSubsystem (Finset.univ : Finset ι)).complementSystem
        P.semanticCode
        (daiLiFiniteSubsystem (Finset.univ : Finset ι)).erasureChannelFromRegister
        recovery := by
  classical
  let threshold := daiLiLargeDistanceThreshold d (Fintype.card ι)
  let endpoints := longInteractionEndpointQubits P embedding threshold
  let endpointSubsystem : FiniteSubsystem ι := ⟨endpoints⟩
  let outsideSubsystem := familyUnionSubsystem
    (fun q : ι => daiLiSingletonSubsystem q) endpointsᶜ
  have hdPos : 0 < d := by omega
  have hEndpointCard : endpoints.card < d := by
    simpa [endpoints, threshold] using
      card_longInteractionEndpointQubits_lt_distance P embedding d hFew hdPos
  obtain ⟨endpointRecovery, hEndpointRecovery⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
      endpointSubsystem (by simpa [endpointSubsystem] using hEndpointCard)
  obtain ⟨outsideRecovery, hOutsideRecovery⟩ :=
    exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled P
      (fun q : ι => daiLiSingletonSubsystem q) endpointsᶜ
      (by
        intro q hq
        apply semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
        change 1 < d
        omega)
      (by
        intro p hp q _hq hpq
        exact daiLiSingletonsOutsideLongEndpoints_fixedGeneratorDecoupled
          P embedding (by simpa [threshold] using hThreshold) hp hpq)
  have hEndpointOutsideDecoupled : P.fixedGeneratorDecoupled
      (endpointSubsystem.selected : Set ι) (outsideSubsystem.selected : Set ι) := by
    refine (P.fixedGeneratorDecoupled_iff_disjoint_no_cross_interaction _ _).2 ⟨?_, ?_⟩
    · apply Set.disjoint_left.mpr
      intro p hp hOutside
      have hpEndpoint : p ∈ endpoints := by simpa [endpointSubsystem] using hp
      have hpOutside : p ∈ endpointsᶜ := by
        simpa [outsideSubsystem, familyUnionSubsystem, daiLiSingletonSubsystem] using hOutside
      exact (Finset.mem_compl.mp hpOutside) hpEndpoint
    · intro p hp q hq j hSupport
      have hqOutside : q ∈ endpointsᶜ := by
        simpa [outsideSubsystem, familyUnionSubsystem, daiLiSingletonSubsystem] using hq
      have hInteraction : P.fixedGeneratorInteraction p q :=
        (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).2
          ⟨by
            intro hpq
            subst q
            exact (Finset.mem_compl.mp hqOutside) (by simpa [endpointSubsystem] using hp),
            j, hSupport.1, hSupport.2⟩
      exact no_fixedGeneratorInteraction_from_outside_longEndpoints_of_threshold_lt_one
        P embedding (by simpa [threshold] using hThreshold)
        (p := q) (q := p) (Finset.mem_compl.mp hqOutside)
        (P.fixedGeneratorInteractionGraph_symmetric hInteraction)
  obtain ⟨recovery, hRecovery⟩ := exists_erasureRecovery_of_fixedGeneratorDecoupled P
    endpointSubsystem outsideSubsystem endpointRecovery outsideRecovery hEndpointRecovery hOutsideRecovery
      hEndpointOutsideDecoupled
  have hAll : unionSubsystem endpointSubsystem outsideSubsystem =
      daiLiFiniteSubsystem (Finset.univ : Finset ι) := by
    apply congrArg (fun selected : Finset ι => (⟨selected⟩ : FiniteSubsystem ι))
    ext q
    simp [endpointSubsystem, outsideSubsystem, familyUnionSubsystem,
      daiLiSingletonSubsystem]
  rw [← hAll]
  exact ⟨recovery, hRecovery⟩
end QEC.Locality
