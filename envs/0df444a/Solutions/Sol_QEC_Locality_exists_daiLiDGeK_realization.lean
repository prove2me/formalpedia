-- Prove2me | solution 1 for QEC.Locality.exists_daiLiDGeK_realization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:25:35.465302+00:00
-- url     : https://prove2.me/submissions/c3ddab15-3ac2-4b8d-906f-6a4e5a2d2353

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_daiLiDGeKResidual_selected_eq
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiDGeKB
import Theorems.Thm_QEC_Locality_daiLiBadGridCells_eq_empty_of_small_longCount
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiDGeKA
import Theorems.Thm_QEC_Locality_exists_daiLiDGeKSeparator_card_bound
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_daiLiBadGridCells_iff
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
attribute [local simp] QEC.Locality.mem_daiLiBadGridCells_iff
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


attribute [local simp] QEC.Locality.daiLiDGeKResidual_selected_eq

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
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d)
    (hThreshold : 1 ≤ threshold) (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (hEll : 0 < ell) (hScale : 4 * ell ≤ w) (hThresholdEll : threshold ≤ ell)
    (hEdge : 1 ≤ 2 * ell) (hLongStrip : 1 ≤ w - 4 * ell)
    (hSmallStrip : 12 * ell * (w - 4 * ell) < d)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hGoodBaseCard : ∀ (t : GridTranslation w) cell,
      cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) →
        (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d) :
    ∃ t : GridTranslation w,
      ((daiLiDGeKSeparator P embedding threshold w ell t).card : ℝ) ≤
          (32 * ell ^ 2 / w ^ 2) * Fintype.card ι +
            64 * ell / w * (P.longInteractionCount embedding threshold : ℝ) ∧
      daiLiBadGridCells P embedding threshold d w (gridOrigin w t) = ∅ ∧
      (∃ recovery : QuantumChannel
          (daiLiDGeKASubsystem P embedding d threshold w ell t).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (daiLiDGeKASubsystem P embedding d threshold w ell t).complementSystem
          P.semanticCode
          (daiLiDGeKASubsystem P embedding d threshold w ell t).erasureChannelFromRegister
          recovery) ∧
      ∃ recovery : QuantumChannel
          (daiLiDGeKBSubsystem P embedding threshold w ell t).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (daiLiDGeKBSubsystem P embedding threshold w ell t).complementSystem
          P.semanticCode
          (daiLiDGeKBSubsystem P embedding threshold w ell t).erasureChannelFromRegister
          recovery := by
  obtain ⟨t, hSeparator⟩ :=
    exists_daiLiDGeKSeparator_card_bound P embedding threshold w ell hEll hScale
  have hLongCount : 2 * P.longInteractionCount embedding threshold < d := by
    rw [← P.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount embedding threshold]
    omega
  have hNoBad := daiLiBadGridCells_eq_empty_of_small_longCount P embedding threshold w d
    (gridOrigin w t) hGlobal
  refine ⟨t, hSeparator, hNoBad, ?_, ?_⟩
  · apply exists_erasureRecovery_daiLiDGeKA P embedding d hDistance threshold w ell t
      hGlobal hThreshold hWidthNat hEllNat hEll (by linarith) hThresholdEll
      baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal hBaseVerticalGood
      hBaseVerticalBad hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal
      hReachVerticalGood hReachVerticalBad
    intro cell hCell
    exact hGoodBaseCard t cell (by simpa using hCell)
    exact hBoundaryBudget
    exact hShortPackingScale
  · exact exists_erasureRecovery_daiLiDGeKB P embedding d hDistance threshold w ell t
      hEll hScale hThresholdEll hEdge hLongStrip hSmallStrip hLongCount
end QEC.Locality
