-- Prove2me | solution 1 for QEC.Locality.exists_daiLiBadInteractionSquareFamilySubdivision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:09:42.333203+00:00
-- url     : https://prove2.me/submissions/ea658a56-0fae-4a04-b37f-742c51770eb0

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_exists_daiLiRectangleAtomization_globalSupport
import Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_atomCounters_sum
import Theorems.Thm_QEC_Locality_daiLiGreedyAtomicSubdivision_family_count
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_counters
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_cover
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_pairwise
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_ordered
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_piece_properties
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    {α : Type*} [DecidableEq α]
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold ell : ℝ) (d : Nat)
    (squares : Finset α) (center : α → ℝ × ℝ) (radius : α → ℝ)
    (hEll : 0 < ell)
    (hHeight : ∀ square ∈ squares, 5 * ell ≤ 2 * radius square)
    (hBad : ∀ square ∈ squares,
      IsBadInteractionSquare P embedding threshold d (center square) (radius square)) :
    ∃ (atoms : α → List (ℝ × ℝ))
      (rectangles : α → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ square ∈ squares,
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((center square).2 - radius square) ((center square).2 + radius square)
          (atoms square)) ∧
      (∀ square ∈ squares,
        rectangles square = daiLiPhysicalGreedyRectangles P embedding threshold
          ((center square).1 - radius square) ((center square).1 + radius square)
          d (atoms square)) ∧
      (∀ square ∈ squares,
        (rectangles square).IsChain (fun first second => first.2.2 = second.1.2)) ∧
      (∀ square ∈ squares,
        DaiLiPairwiseDisjointQubitRectangles embedding (rectangles square)) ∧
      (∀ square ∈ squares,
        daiLiRectangleQubitsCover embedding (rectangles square) =
          squareQubits embedding (center square) (radius square)) ∧
      (∀ square ∈ squares, ∀ rectangle ∈ rectangles square,
        5 * ell ≤ rectangle.2.2 - rectangle.1.2 ∧
          (10 * regionInteractionCounter P embedding threshold
              (embedding.qubitsInRectangle rectangle.1 rectangle.2) ≤ d ∨
            rectangle.2.2 - rectangle.1.2 ≤ 10 * ell)) ∧
      (∑ square ∈ squares, (rectangles square).length) * d ≤
        30 * ∑ square ∈ squares,
          regionInteractionCounter P embedding threshold
            (squareQubits embedding (center square) (radius square)) := by
  let atomWitness : ∀ square (hSquare : square ∈ squares),
      ∃ atoms, DaiLiHorizontalAtomization
        (daiLiGlobalVerticalQubitSupport embedding) ell
        ((center square).2 - radius square) ((center square).2 + radius square) atoms :=
    fun square hSquare =>
      exists_daiLiRectangleAtomization_globalSupport embedding
        ((center square).1 - radius square, (center square).2 - radius square)
        ((center square).1 + radius square, (center square).2 + radius square)
        ell hEll (by linarith [hHeight square hSquare])
  let atoms : α → List (ℝ × ℝ) := fun square =>
    if hSquare : square ∈ squares then Classical.choose (atomWitness square hSquare) else []
  have hAtoms : ∀ square ∈ squares,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((center square).2 - radius square) ((center square).2 + radius square)
        (atoms square) := by
    intro square hSquare
    simp only [atoms, dif_pos hSquare]
    exact Classical.choose_spec (atomWitness square hSquare)
  let rectangles : α → List ((ℝ × ℝ) × (ℝ × ℝ)) := fun square =>
    daiLiPhysicalGreedyRectangles P embedding threshold
      ((center square).1 - radius square) ((center square).1 + radius square)
      d (atoms square)
  refine ⟨atoms, rectangles, hAtoms, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro square hSquare
    rfl
  · intro square hSquare
    simpa [rectangles] using daiLiPhysicalGreedyRectangles_ordered
      P embedding threshold ((center square).1 - radius square)
        ((center square).1 + radius square) (hAtoms square hSquare) d
  · intro square hSquare
    simpa [rectangles] using daiLiPhysicalGreedyRectangles_pairwise
      P embedding threshold ((center square).1 - radius square)
        ((center square).1 + radius square) ell hEll (hAtoms square hSquare) d
  · intro square hSquare
    simpa [rectangles, squareQubits] using daiLiPhysicalGreedyRectangles_cover
      P embedding threshold ((center square).1 - radius square)
        ((center square).1 + radius square) ell hEll (hAtoms square hSquare) d
  · intro square hSquare rectangle hRectangle
    simpa [rectangles] using daiLiPhysicalGreedyRectangles_piece_properties
      P embedding threshold ((center square).1 - radius square)
        ((center square).1 + radius square) ell hEll (hAtoms square hSquare) d
        rectangle hRectangle
  · have hBadAtoms : ∀ square ∈ squares,
      d ≤ 10 * (daiLiAtomCounters P embedding threshold
        ((center square).1 - radius square) ((center square).1 + radius square)
        (atoms square)).sum := by
      intro square hSquare
      rw [(hAtoms square hSquare).atomCounters_sum P embedding threshold
        ((center square).1 - radius square) ((center square).1 + radius square) hEll]
      exact hBad square hSquare
    have hLengths : ∀ square ∈ squares,
        (rectangles square).length =
          (daiLiGreedyAtomicSubdivision d
            (daiLiAtomCounters P embedding threshold
              ((center square).1 - radius square) ((center square).1 + radius square)
              (atoms square))).length := by
      intro square hSquare
      have hLengths := congrArg List.length
        (daiLiPhysicalGreedySubdivision_counters P embedding threshold
          ((center square).1 - radius square) ((center square).1 + radius square)
          d (atoms square))
      simpa [rectangles, daiLiPhysicalGreedyRectangles] using hLengths
    calc
      (∑ square ∈ squares, (rectangles square).length) * d =
          (∑ square ∈ squares, (daiLiGreedyAtomicSubdivision d
            (daiLiAtomCounters P embedding threshold
              ((center square).1 - radius square) ((center square).1 + radius square)
              (atoms square))).length) * d := by
        apply congrArg (fun count : Nat => count * d)
        apply Finset.sum_congr rfl
        intro square hSquare
        exact hLengths square hSquare
      _ ≤
          30 * ∑ square ∈ squares,
            (daiLiAtomCounters P embedding threshold
              ((center square).1 - radius square) ((center square).1 + radius square)
              (atoms square)).sum := by
        exact daiLiGreedyAtomicSubdivision_family_count d
          (fun square => daiLiAtomCounters P embedding threshold
            ((center square).1 - radius square) ((center square).1 + radius square)
            (atoms square)) squares hBadAtoms
      _ = 30 * ∑ square ∈ squares,
          regionInteractionCounter P embedding threshold
            (squareQubits embedding (center square) (radius square)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro square hSquare
        rw [(hAtoms square hSquare).atomCounters_sum P embedding threshold
          ((center square).1 - radius square) ((center square).1 + radius square) hEll]
        rfl
end QEC.Locality
