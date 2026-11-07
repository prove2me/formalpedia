-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.violatedGenerators_primalSweepPrefix_subset_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:55:52.465641+00:00
-- url     : https://prove2.me/submissions/b987434a-088a-4b1a-a886-db7976830c66

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalXYMembrane_eq_indicator_sweepPlaquettes
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSweepRegion_subset
import Theorems.Thm_QEC_Coding_PeriodicCubical4_restrict_primalMembrane_vector_eq_prefix
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliErrorPath_accumulate_nil
import Theorems.Thm_QEC_Coding_PauliErrorPath_accumulate_singleton
import Theorems.Thm_QEC_Coding_PauliErrorPath_append_increments
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_empty
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_reverse
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_singleton
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_take
import Theorems.Thm_QEC_Coding_PauliErrorPath_reverse_increments
import Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_length
import Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_zero
import Theorems.Thm_QEC_Coding_PauliErrorPath_states_getLast_eq_some
import Theorems.Thm_QEC_Coding_PauliErrorPath_states_head_eq_some
import Theorems.Thm_QEC_Coding_PauliErrorPath_states_length
import Theorems.Thm_QEC_Coding_PauliErrorPath_take_increments
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalZLogical_in_normalizer
import Theorems.Thm_QEC_Coding_PeriodicCubical4_syndromeSupport_primalMembrane
import Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_code
import Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_generators
import Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_term
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_cons_cons
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_nil
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_singleton
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_length_rowMajorExactPath_increments
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_movingFrontier_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openHorizontalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openVerticalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_periodicHorizontalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_periodicVerticalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_rowMajorPrefix_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_seamFrontier_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_rowMajorExactPath_endpoint
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_rowMajorPrefix_row_bounds
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_cons_cons
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_nil
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_singleton
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_support_restrictBinaryTo_subset_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_binaryDagger
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_length_alternatingWidths
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_incidentGeneratorUnion_of_mem_generatorSupport
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_regionUnion_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_syndromeSupport
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_violatedGenerators
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_not_commutes_complement_of_not_commutes_restriction
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_pathHeight_empty
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_sum_alternatingWidths
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeSupport_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeWeight_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_unitDefectEnergy_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_binaryDagger
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_eq_of_vector_eq
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_eq_syndromeSupport
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_commutes_of_disjoint_support
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_restrictBinaryTo_vector_add_of_support_subset_union
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
import Theorems.Thm_QEC_Locality_support_restrictBinaryTo_subset
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
attribute [local simp] QEC.Coding.PauliErrorPath.accumulate_nil
attribute [local simp] QEC.Coding.PauliErrorPath.accumulate_singleton
attribute [local simp] QEC.Coding.PauliErrorPath.append_increments
attribute [local simp] QEC.Coding.PauliErrorPath.endpoint_empty
attribute [local simp] QEC.Coding.PauliErrorPath.endpoint_reverse
attribute [local simp] QEC.Coding.PauliErrorPath.endpoint_singleton
attribute [local simp] QEC.Coding.PauliErrorPath.endpoint_take
attribute [local simp] QEC.Coding.PauliErrorPath.reverse_increments
attribute [local simp] QEC.Coding.PauliErrorPath.stateAt_length
attribute [local simp] QEC.Coding.PauliErrorPath.stateAt_zero
attribute [local simp] QEC.Coding.PauliErrorPath.states_getLast_eq_some
attribute [local simp] QEC.Coding.PauliErrorPath.states_head_eq_some
attribute [local simp] QEC.Coding.PauliErrorPath.states_length
attribute [local simp] QEC.Coding.PauliErrorPath.take_increments
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.PeriodicCubical4.toricHamiltonian_code
attribute [local simp] QEC.Coding.PeriodicCubical4.toricHamiltonian_generators
attribute [local simp] QEC.Coding.PeriodicCubical4.toricHamiltonian_term
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_cons_cons
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_nil
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_singleton
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.length_rowMajorExactPath_increments
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_movingFrontier_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openHorizontalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openVerticalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_periodicHorizontalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_periodicVerticalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_rowMajorPrefix_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_seamFrontier_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.rowMajorExactPath_endpoint
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_cons_cons
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_nil
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_singleton
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_binaryDagger
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_binaryOne
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.length_alternatingWidths
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_regionUnion_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_syndromeSupport
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_violatedGenerators
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pathHeight_empty
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.sum_alternatingWidths
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeSupport_binaryOne
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeWeight_binaryOne
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.unitDefectEnergy_binaryOne
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_binaryDagger
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_binaryOne
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


section
noncomputable section
namespace QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
private theorem fin_add_one_val_cases (i : Fin L) :
    (i + 1).val = i.val + 1 ∨
      ((i + 1).val = 0 ∧ i.val + 1 = L) := by
  by_cases hi : i.val + 1 < L
  · left
    simp [Fin.add_def, Nat.mod_eq_of_lt hi]
  · right
    have hiL : i.val + 1 = L := by omega
    simp [Fin.add_def, hiL]
private theorem mem_periodicHorizontalInterval_two_of_row_eq_or_succ
    (a : Fin L) (p : SweepSite L)
    (hp : p.2 = a ∨ p.2 = a + 1) :
    p ∈ StripGeometry.periodicHorizontalInterval L a.val 2 := by
  rw [StripGeometry.mem_periodicHorizontalInterval_iff]
  have ha : a.val % L = a.val := Nat.mod_eq_of_lt a.isLt
  rw [ha]
  rcases hp with rfl | hp
  · left
    omega
  · rw [hp]
    rcases fin_add_one_val_cases a with hnext | ⟨hzero, hwrap⟩
    · left
      omega
    · right
      omega
private theorem fin_eq_or_succ_of_finEquiv_eq_or_add_one
    (a : ZMod L) (i : Fin L)
    (hi : (ZMod.finEquiv L) i = a ∨
      (ZMod.finEquiv L) i = a + 1) :
    i = (ZMod.finEquiv L).symm a ∨
      i = (ZMod.finEquiv L).symm a + 1 := by
  rcases hi with hi | hi
  · left
    exact (ZMod.finEquiv L).injective
      (hi.trans ((ZMod.finEquiv L).apply_symm_apply a).symm)
  · right
    apply (ZMod.finEquiv L).injective
    rw [(ZMod.finEquiv L).map_add,
      (ZMod.finEquiv L).apply_symm_apply, map_one]
    exact hi
private theorem primal_link_slice_row_interval
    (z w : ZMod L) (e : Link L) :
    ∃ start : Nat, ∀ p : SweepSite L,
      primalSweepPlaquette z w p ∈ linkPlaquettes e →
        p ∈ StripGeometry.periodicHorizontalInterval L start 2 := by
  rcases e with ⟨c, a⟩
  cases a with
  | x =>
      let base : Fin L := (ZMod.finEquiv L).symm (c .y - 1)
      refine ⟨base.val, fun p hp => ?_⟩
      simp [linkPlaquettes, primalSweepPlaquette, unshift] at hp
      apply mem_periodicHorizontalInterval_two_of_row_eq_or_succ base p
      apply fin_eq_or_succ_of_finEquiv_eq_or_add_one (c .y - 1) p.2
      rcases hp with hp | hp
      · right
        have hy := congrFun hp .y
        simpa using hy
      · left
        have hy := congrFun hp .y
        simpa using hy
  | y =>
      let base : Fin L := (ZMod.finEquiv L).symm (c .y)
      refine ⟨base.val, fun p hp => ?_⟩
      simp [linkPlaquettes, primalSweepPlaquette, unshift] at hp
      apply mem_periodicHorizontalInterval_two_of_row_eq_or_succ base p
      left
      apply (ZMod.finEquiv L).injective
      rw [(ZMod.finEquiv L).apply_symm_apply]
      rcases hp with hp | hp
      · exact congrFun hp .y
      · simpa using congrFun hp .y
  | z =>
      refine ⟨0, fun p hp => ?_⟩
      simp [linkPlaquettes, primalSweepPlaquette, unshift] at hp
  | w =>
      refine ⟨0, fun p hp => ?_⟩
      simp [linkPlaquettes, primalSweepPlaquette, unshift] at hp
private theorem mem_sweepSiteFrontier_of_periodic_crossing
    (n start : Nat) (p q : SweepSite L)
    (hpInterval :
      p ∈ StripGeometry.periodicHorizontalInterval L start 2)
    (hqInterval :
      q ∈ StripGeometry.periodicHorizontalInterval L start 2)
    (hpCursor : p.2.val ≤ n / L) (hCursorQ : n / L ≤ q.2.val) :
    p ∈ sweepSiteFrontier L n := by
  have hpStrip :
      p ∈ StripGeometry.openVerticalInterval L 0 L := by
    simp [StripGeometry.openVerticalInterval]
  have hpRows :=
    (StripGeometry.mem_periodicHorizontalInterval_iff p).1 hpInterval
  have hqRows :=
    (StripGeometry.mem_periodicHorizontalInterval_iff q).1 hqInterval
  rw [sweepSiteFrontier, Finset.mem_union,
    StripGeometry.mem_movingFrontier_iff,
    StripGeometry.mem_seamFrontier_iff]
  rcases hpRows with hpMain | hpWrap
  · rcases hqRows with hqMain | hqWrap
    · left
      exact ⟨hpStrip, hpCursor, by omega⟩
    · by_cases hpr : p.2.val < 2
      · right
        exact ⟨hpStrip, hpr⟩
      · left
        exact ⟨hpStrip, hpCursor, by omega⟩
  · right
    refine ⟨hpStrip, ?_⟩
    have hL : 0 < L := NeZero.pos L
    have hstartLt : start % L < L := Nat.mod_lt start hL
    omega
private theorem support_restrictBinaryTo_subset_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Finset ι) (Q : Binary ι) :
    support (Locality.restrictBinaryTo R Q) ⊆ support Q := by
  intro p hp
  rw [mem_support] at hp ⊢
  rcases hp with hpX | hpZ
  · left
    simp [xSupport, Locality.restrictBinaryTo, binarySupport] at hpX
    simpa [xSupport, binarySupport] using hpX.2
  · right
    simp [zSupport, Locality.restrictBinaryTo, binarySupport] at hpZ
    simpa [zSupport, binarySupport] using hpZ.2
end QEC.Coding.PeriodicCubical4
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    (z w : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    (toricHamiltonian (L := L)).violatedGenerators
        (primalMembraneError (primalSweepPrefix z w n)) ⊆
      (toricHamiltonian (L := L)).incidentGeneratorUnion
        (primalSweepFrontier z w n) := by
  intro j hj
  let R := primalSweepRegion z w n
  let Q := primalMembraneError (primalXYMembrane z w)
  let E := Locality.restrictBinaryTo R Q
  let F := Locality.restrictBinaryTo Rᶜ Q
  have hEVector :
      E.vector = (primalMembraneError (primalSweepPrefix z w n)).vector := by
    simpa [E, Q, R] using restrict_primalMembrane_vector_eq_prefix z w n
  have hjE : j ∈ (toricHamiltonian (L := L)).violatedGenerators E := by
    rw [(toricHamiltonian (L := L)).violatedGenerators_eq_of_vector_eq
      E (primalMembraneError (primalSweepPrefix z w n)) hEVector]
    exact hj
  rw [mem_violatedGenerators] at hjE
  have hnotDisjointE :
      ¬ Disjoint (support E)
        (support ((toricHamiltonian (L := L)).generators j)) := by
    intro hdisjoint
    exact hjE (QEC.Locality.commutes_of_disjoint_support E
      ((toricHamiltonian (L := L)).generators j) hdisjoint)
  obtain ⟨p, hpE, hpGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointE
  have hpR : p ∈ R :=
    Locality.support_restrictBinaryTo_subset R Q hpE
  have hRDisjoint : Disjoint R Rᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hiR hiCompl
    exact (Finset.mem_compl.mp hiCompl) hiR
  have hQCover : support Q ⊆ R ∪ Rᶜ := by
    intro i _hi
    by_cases hiR : i ∈ R
    · exact Finset.mem_union_left _ hiR
    · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hiR)
  have hdecomp : Q.vector = E.vector + F.vector :=
    Locality.restrictBinaryTo_vector_add_of_support_subset_union
      R Rᶜ Q hRDisjoint hQCover
  have hQNormalizer :
      (toricHamiltonian (L := L)).code.1.InBinaryNormalizer Q := by
    intro S hS
    apply primalZLogical_in_normalizer z w S
    have hS' :
        S ∈ (toricSourceValidCode (L := L)).1.generatedGroup := by
      simpa [toricHamiltonian_code, Q, primalZLogical,
        primalMembraneError] using hS
    have hgen :
        S ∈ generatedStabilizerSet (toricGenerator (L := L)) := by
      rw [toricGenerator_generated_eq]
      exact hS'
    simpa [generatedStabilizerSet] using hgen
  have hFNotCommutes :
      ¬ Commutes F ((toricHamiltonian (L := L)).generators j) :=
    (toricHamiltonian (L := L)).not_commutes_complement_of_not_commutes_restriction
      Q E F j hQNormalizer hdecomp hjE
  have hnotDisjointF :
      ¬ Disjoint (support F)
        (support ((toricHamiltonian (L := L)).generators j)) := by
    intro hdisjoint
    exact hFNotCommutes
      (QEC.Locality.commutes_of_disjoint_support F
        ((toricHamiltonian (L := L)).generators j) hdisjoint)
  obtain ⟨q, hqF, hqGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointF
  have hqCompl : q ∈ Rᶜ :=
    Locality.support_restrictBinaryTo_subset Rᶜ Q hqF
  have hqNotR : q ∉ R := Finset.mem_compl.mp hqCompl
  have hqQ : q ∈ support Q :=
    support_restrictBinaryTo_subset_support Rᶜ Q hqF
  have hpAll : p ∈ (primalSweepPlaquettes z w).toFinset :=
    primalSweepRegion_subset z w n (by simpa [R] using hpR)
  have hqAll : q ∈ (primalSweepPlaquettes z w).toFinset := by
    change q ∈ support (primalMembraneError (primalXYMembrane z w)) at hqQ
    rw [primalMembraneError, support_cssZCheck, hammingSupport] at hqQ
    have hqValue : primalXYMembrane z w q ≠ 0 :=
      (Finset.mem_filter.mp hqQ).2
    by_contra hq
    simp [primalXYMembrane_eq_indicator_sweepPlaquettes, hq] at hqValue
  rcases List.mem_map.mp (List.mem_toFinset.mp hpAll) with
    ⟨ps, _hps, rfl⟩
  rcases List.mem_map.mp (List.mem_toFinset.mp hqAll) with
    ⟨qs, _hqs, rfl⟩
  have hpsPrefix : ps ∈ StripGeometry.rowMajorPrefix L n := by
    rw [StripGeometry.mem_rowMajorPrefix_iff]
    have hmem :=
      (primalSweepPlaquette_mem_sweepRegion_iff z w ps n).1
        (by simpa [R] using hpR)
    simpa [min_eq_left hn] using hmem
  have hqsNotPrefix : qs ∉ StripGeometry.rowMajorPrefix L n := by
    rw [StripGeometry.mem_rowMajorPrefix_iff]
    intro hindex
    apply hqNotR
    have hmem : StripGeometry.rowMajorIndex qs < min n (L * L) := by
      simpa [min_eq_left hn] using hindex
    simpa [R] using
      (primalSweepPlaquette_mem_sweepRegion_iff z w qs n).2 hmem
  have hRows := StripGeometry.rowMajorPrefix_row_bounds
    (NeZero.pos L) ps qs hpsPrefix hqsNotPrefix
  cases j with
  | inl e =>
      rw [toricHamiltonian_generators, toricGenerator_support_inl] at hpGenerator hqGenerator
      obtain ⟨start, hinterval⟩ := primal_link_slice_row_interval z w e
      have hpsFrontier : ps ∈ sweepSiteFrontier L n :=
        mem_sweepSiteFrontier_of_periodic_crossing n start ps qs
          (hinterval ps hpGenerator) (hinterval qs hqGenerator)
          hRows.1 hRows.2
      have hpFrontier :
          primalSweepPlaquette z w ps ∈ primalSweepFrontier z w n := by
        exact Finset.mem_image.mpr ⟨ps, hpsFrontier, rfl⟩
      have hpGeneratorSupport :
          primalSweepPlaquette z w ps ∈
            support ((toricHamiltonian (L := L)).generators (Sum.inl e)) := by
        rw [toricHamiltonian_generators, toricGenerator_support_inl]
        exact hpGenerator
      exact
        (toricHamiltonian (L := L)).mem_incidentGeneratorUnion_of_mem_generatorSupport
          _ (primalSweepPlaquette z w ps) (Sum.inl e)
            hpFrontier hpGeneratorSupport
  | inr c =>
      exfalso
      rw [(toricHamiltonian (L := L)).violatedGenerators_eq_syndromeSupport,
        syndromeSupport_primalMembrane] at hj
      simp at hj
end QEC.Coding.PeriodicCubical4
