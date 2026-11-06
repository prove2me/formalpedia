-- Prove2me | solution 1 for QEC.Locality.card_centeredRectangleGeneralGrowthBoundary_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:54:55.943466+00:00
-- url     : https://prove2.me/submissions/5fbd201a-c8b9-4848-b7dc-ce8bb3e21742

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_card_longOutsideNeighborsOf_le_sum_counter
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_card_centeredRectangle_shell_le
import Theorems.Thm_QEC_Locality_centeredRectangle_shell_subset_of_inset
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
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ)
    (hThreshold : 1 ≤ threshold)
    (hOuterHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hOuterVertical : 1 ≤ 2 * outerVerticalRadius)
    (hHorizontalInset : outerHorizontalRadius - threshold ≤ innerHorizontalRadius)
    (hVerticalInset : outerVerticalRadius - threshold ≤ innerVerticalRadius) :
    ((centeredRectangleGeneralGrowthBoundary P embedding center
      innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold).selected.card : ℝ) ≤
      48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          innerHorizontalRadius innerVerticalRadius,
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
  let newShell := centeredRectangleQubits embedding center
    outerHorizontalRadius outerVerticalRadius \
      centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius
  let collar := centeredRectangleExternalCollar embedding center
    outerHorizontalRadius outerVerticalRadius threshold
  let longOutside := longOutsideNeighborsOf P embedding threshold
    (centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius)
  have hNewShellSubset := centeredRectangle_shell_subset_of_inset embedding center
    innerHorizontalRadius innerVerticalRadius outerHorizontalRadius outerVerticalRadius
    threshold hHorizontalInset hVerticalInset
  have hNewShellReal :
      ((centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius).card : ℝ) ≤
      ((centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hNewShellSubset
  have hNewShell' : (newShell.card : ℝ) ≤
      ((centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold)).card : ℝ) := by
    simpa [newShell] using hNewShellReal
  have hNewShell : (newShell.card : ℝ) ≤
      24 * (outerHorizontalRadius + outerVerticalRadius) * threshold := by
    exact hNewShell'.trans
      (card_centeredRectangle_shell_le embedding center
        outerHorizontalRadius outerVerticalRadius threshold hThreshold
        hOuterHorizontal hOuterVertical)
  have hExpandedHorizontal : 1 ≤ 2 * (outerHorizontalRadius + threshold) := by
    nlinarith
  have hExpandedVertical : 1 ≤ 2 * (outerVerticalRadius + threshold) := by
    nlinarith
  have hCollarRaw := card_centeredRectangle_shell_le embedding center
    (outerHorizontalRadius + threshold) (outerVerticalRadius + threshold)
    threshold hThreshold hExpandedHorizontal hExpandedVertical
  have hCollar : (collar.card : ℝ) ≤
      24 * ((outerHorizontalRadius + threshold) +
        (outerVerticalRadius + threshold)) * threshold := by
    dsimp [collar, centeredRectangleExternalCollar]
    convert hCollarRaw using 1 <;> ring
  have hLong : (longOutside.card : ℝ) ≤
      ((∑ q ∈ centeredRectangleQubits embedding center
        innerHorizontalRadius innerVerticalRadius,
        P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
    dsimp [longOutside]
    exact_mod_cast card_longOutsideNeighborsOf_le_sum_counter P embedding threshold
      (centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius)
  have hUnionNat :
      ((newShell ∪ collar) ∪ longOutside).card ≤
        newShell.card + collar.card + longOutside.card := by
    calc
      _ ≤ (newShell ∪ collar).card + longOutside.card := Finset.card_union_le _ _
      _ ≤ (newShell.card + collar.card) + longOutside.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := by omega
  have hUnion :
      (((newShell ∪ collar) ∪ longOutside).card : ℝ) ≤
        (newShell.card : ℝ) + (collar.card : ℝ) + (longOutside.card : ℝ) := by
    exact_mod_cast hUnionNat
  change (((newShell ∪ collar) ∪ longOutside).card : ℝ) ≤ _
  calc
    _ ≤ (newShell.card : ℝ) + (collar.card : ℝ) + (longOutside.card : ℝ) := hUnion
    _ ≤ 24 * (outerHorizontalRadius + outerVerticalRadius) * threshold +
          24 * ((outerHorizontalRadius + threshold) +
            (outerVerticalRadius + threshold)) * threshold +
          ((∑ q ∈ centeredRectangleQubits embedding center
            innerHorizontalRadius innerVerticalRadius,
            P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
      linarith
    _ = _ := by ring
end QEC.Locality
