-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_centeredRectangle_general_growth_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:57:13.710229+00:00
-- url     : https://prove2.me/submissions/e108b232-27de-4c3c-8801-a267f33712b1

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_fixedGeneratorOuterBoundary_centeredRectangle_subset_generalGrowthBoundary
import Theorems.Thm_QEC_Locality_centeredRectangleSubsystem_subset_inner_union_generalGrowthBoundary
import Theorems.Thm_QEC_Locality_card_centeredRectangleGeneralGrowthBoundary_le
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
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
import Theorems.Thm_QEC_Locality_exists_qudit_erasureRecovery_of_subset
import Theorems.Thm_QEC_Locality_semanticStabilizerDistance_erasureRecoverableFromRegister
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


attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ)
    (hThreshold : 1 ≤ threshold)
    (hOuterHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hOuterVertical : 1 ≤ 2 * outerVerticalRadius)
    (hHorizontal : innerHorizontalRadius ≤ outerHorizontalRadius)
    (hVertical : innerVerticalRadius ≤ outerVerticalRadius)
    (hHorizontalInset : outerHorizontalRadius - threshold ≤ innerHorizontalRadius)
    (hVerticalInset : outerVerticalRadius - threshold ≤ innerVerticalRadius)
    (hBoundarySmall :
      48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          innerHorizontalRadius innerVerticalRadius,
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d)
    (hRecoveryInner :
      ∃ recovery : QuantumChannel
          (centeredRectangleSubsystem embedding center innerHorizontalRadius
            innerVerticalRadius).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (centeredRectangleSubsystem embedding center innerHorizontalRadius
            innerVerticalRadius).complementSystem
          P.semanticCode
          (centeredRectangleSubsystem embedding center innerHorizontalRadius
            innerVerticalRadius).erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        P.semanticCode
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).erasureChannelFromRegister recovery := by
  let inner := centeredRectangleSubsystem embedding center
    innerHorizontalRadius innerVerticalRadius
  let boundary := centeredRectangleGeneralGrowthBoundary P embedding center
    innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
    outerVerticalRadius threshold
  have hBoundaryCardReal : (boundary.selected.card : ℝ) < d :=
    (card_centeredRectangleGeneralGrowthBoundary_le P embedding center
      innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold hThreshold hOuterHorizontal hOuterVertical
      hHorizontalInset hVerticalInset).trans_lt hBoundarySmall
  have hBoundaryCard : boundary.selected.card < d := by
    exact_mod_cast hBoundaryCardReal
  obtain ⟨recoveryInner, hRecoveryInner'⟩ := hRecoveryInner
  obtain ⟨recoveryBoundary, hRecoveryBoundary⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister
      P.code d hDistance boundary hBoundaryCard
  have hOuterBoundary :
      P.fixedGeneratorOuterBoundary (inner.selected : Set ι) ⊆
        (boundary.selected : Set ι) := by
    simpa [inner, boundary] using
      fixedGeneratorOuterBoundary_centeredRectangle_subset_generalGrowthBoundary
        P embedding center innerHorizontalRadius innerVerticalRadius
          outerHorizontalRadius outerVerticalRadius threshold hHorizontal hVertical
  obtain ⟨recoveryExpanded, hRecoveryExpanded⟩ :=
    exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
      P inner boundary recoveryInner recoveryBoundary
      (by simpa [inner] using hRecoveryInner')
      (by simpa [boundary,
        StabilizerCode.BinaryStabilizerPresentation.semanticCode] using hRecoveryBoundary)
      hOuterBoundary
  exact
    (exists_qudit_erasureRecovery_of_subset
      (quditSubsystemOfFinite (centeredRectangleSubsystem embedding center
        outerHorizontalRadius outerVerticalRadius))
      (quditSubsystemOfFinite (unionSubsystem inner boundary))
      (by exact
        (centeredRectangleSubsystem_subset_inner_union_generalGrowthBoundary
          P embedding center innerHorizontalRadius innerVerticalRadius
            outerHorizontalRadius outerVerticalRadius threshold))
      P.semanticCode ⟨recoveryExpanded, hRecoveryExpanded⟩)
end QEC.Locality
