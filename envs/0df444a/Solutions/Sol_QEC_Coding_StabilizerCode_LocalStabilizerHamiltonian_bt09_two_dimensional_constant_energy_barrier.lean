-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.bt09_two_dimensional_constant_energy_barrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:26:36.060577+00:00
-- url     : https://prove2.me/submissions/208dd721-0835-4dc6-b788-94fd3584c038

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Results_QuantumMemory_TwoDimensionalEnergyBarrier
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
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_cons_cons
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_nil
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_singleton
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_binaryDagger
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_bt09_open_strip_logical_of_two_le_range
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_bt09_periodic_strip_logical_of_two_le_range
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_open_rowMajor_logical_path
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_periodic_rowMajor_logical_path
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_length_alternatingWidths
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_logicalEnergyBarrier_le_pathHeight
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_regionUnion_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_syndromeSupport
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_violatedGenerators
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_pathHeight_empty
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_pathHeight_rowMajorExactPath_le_full_lattice
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_sum_alternatingWidths
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeSupport_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeWeight_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_unitDefectEnergy_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_binaryDagger
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_binaryOne
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
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



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u
variable {κ : Type u} [Fintype κ]
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    {L r : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L) (hr : 2 ≤ r)
    (hBoundary :
      (StripGeometry.HasOpenIntervalGeneratorSupport H r ∧
        StripGeometry.HasOpenRowIntervalGeneratorSupport H r) ∨
      (StripGeometry.HasPeriodicIntervalGeneratorSupport H r ∧
        StripGeometry.HasPeriodicRowIntervalGeneratorSupport H r))
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    H.logicalEnergyBarrier ≤
      8 * r ^ 4 * H.participationBound := by
  by_cases hLarge : 2 * (r - 1) ^ 2 ≤ L
  · have hrOne : 1 ≤ r := by omega
    have hrrOne : 1 ≤ r * r := by
      simpa using Nat.mul_le_mul hrOne hrOne
    have hrrLePow : r * r ≤ r ^ 4 := by
      calc
        r * r = (r * r) * 1 := by simp
        _ ≤ (r * r) * (r * r) :=
          Nat.mul_le_mul_left (r * r) hrrOne
        _ = r ^ 4 := by ring
    rcases hBoundary with hOpen | hPeriodic
    · obtain ⟨start, width, hwidth, Q,
        hQNormalizer, hQNontrivial, hQSupport⟩ :=
        H.exists_bt09_open_strip_logical_of_two_le_range
          hr hLarge hOpen.1 P hPNormalizer hPNontrivial
      have hwidthLe : width ≤ r := by
        rcases hwidth with rfl | rfl <;> omega
      obtain ⟨γ, _hEndpoint, hLogical, hHeight⟩ :=
        H.exists_open_rowMajor_logical_path
          hL hwidthLe hOpen.2 Q hQNormalizer hQNontrivial hQSupport
      exact
        (H.logicalEnergyBarrier_le_pathHeight γ hLogical).trans
          (hHeight.trans (by
            apply Nat.mul_le_mul_right H.participationBound
            calc
              2 * r * r = 2 * (r * r) := by ring
              _ ≤ 2 * r ^ 4 := Nat.mul_le_mul_left 2 hrrLePow
              _ ≤ 8 * r ^ 4 := by omega))
    · obtain ⟨start, width, hwidth, Q,
        hQNormalizer, hQNontrivial, hQSupport⟩ :=
        H.exists_bt09_periodic_strip_logical_of_two_le_range
          hr hLarge hPeriodic.1 P hPNormalizer hPNontrivial
      have hwidthLe : width ≤ r := by
        rcases hwidth with rfl | rfl <;> omega
      obtain ⟨γ, _hEndpoint, hLogical, hHeight⟩ :=
        H.exists_periodic_rowMajor_logical_path
          hL hwidthLe hPeriodic.2 Q hQNormalizer hQNontrivial hQSupport
      exact
        (H.logicalEnergyBarrier_le_pathHeight γ hLogical).trans
          (hHeight.trans (by
            apply Nat.mul_le_mul_right H.participationBound
            calc
              4 * r * r = 4 * (r * r) := by ring
              _ ≤ 4 * r ^ 4 := Nat.mul_le_mul_left 4 hrrLePow
              _ ≤ 8 * r ^ 4 := by omega))
  · let γ := StripGeometry.rowMajorExactPath P
    have hLogical : H.HasLogicalEndpoint γ := by
      change
        H.code.1.InBinaryNormalizer γ.endpoint ∧
          ¬ H.code.1.InGeneratedGroupUpToSign γ.endpoint
      rw [show γ.endpoint = P by
        exact StripGeometry.rowMajorExactPath_endpoint P]
      exact ⟨hPNormalizer, hPNontrivial⟩
    have hNaive :
        H.pathHeight γ ≤
          2 * (L * L) * H.participationBound :=
      H.pathHeight_rowMajorExactPath_le_full_lattice P
    have hLBound : L ≤ 2 * r * r := by
      push Not at hLarge
      have hsub : r - 1 ≤ r := Nat.sub_le r 1
      have hsq : (r - 1) * (r - 1) ≤ r * r :=
        Nat.mul_le_mul hsub hsub
      calc
        L ≤ 2 * (r - 1) ^ 2 := hLarge.le
        _ ≤ 2 * (r * r) := by
          exact Nat.mul_le_mul_left 2 (by simpa [pow_two] using hsq)
        _ = 2 * r * r := by ring
    have hSquare : L * L ≤ (2 * r * r) * (2 * r * r) :=
      Nat.mul_le_mul hLBound hLBound
    have hCoefficient : 2 * (L * L) ≤ 8 * r ^ 4 := by
      calc
        2 * (L * L) ≤ 2 * ((2 * r * r) * (2 * r * r)) :=
          Nat.mul_le_mul_left 2 hSquare
        _ = 8 * r ^ 4 := by ring
    exact
      (H.logicalEnergyBarrier_le_pathHeight γ hLogical).trans
        (hNaive.trans (by
          exact Nat.mul_le_mul_right H.participationBound hCoefficient))
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
