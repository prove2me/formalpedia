-- Prove2me | solution 1 for QEC.Locality.exceptionalBad_separated_from_gridSideStrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:27:44.010407+00:00
-- url     : https://prove2.me/submissions/88dadc62-d86c-453c-9fda-29c0f63cc28b

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_daiLiDGeKResidual_selected_eq
import Theorems.Thm_QEC_Locality_exceptionalBad_not_mem_daiLiDGeKBPrime
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_addCircle_coe_add_int_mul_period
import Theorems.Thm_QEC_Locality_addCircle_dist_le_abs_sub
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_daiLiBadGridCells_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_phase_gridOrigin
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
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (hw : 0 < w)
    (p q : ι) (side : DaiLiGridSideIndex)
    (hp : p ∈ daiLiDGeKExceptionalBadQubits P embedding threshold w ell t)
    (hq : q ∈ daiLiGridSideStripQubits embedding w ell (2 * ell)
      (gridOrigin w t) side) :
    ell ≤ embedding.distance p q := by
  classical
  have hpNotSeparator : p ∉ daiLiDGeKSeparator P embedding threshold w ell t :=
    (Finset.mem_sdiff.mp hp).2
  have hpNotVertex : ¬ vertexBad w (2 * ell) t (embedding.point p) := by
    intro hVertex
    apply hpNotSeparator
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hVertex⟩
  have hpNotWide := exceptionalBad_not_mem_daiLiDGeKBPrime
    P embedding threshold w ell t p hp
  have hpNotEdge : ¬ edgeBad w (2 * ell) t (embedding.point p) := by
    intro hEdge
    apply hpNotWide
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpNotVertex, hEdge⟩
  have hCoordinateX : |(embedding.point p).1 - (embedding.point q).1| ≤
      embedding.distance p q := by
    rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg ((embedding.point p).2 - (embedding.point q).2)]
  have hCoordinateY : |(embedding.point p).2 - (embedding.point q).2| ≤
      embedding.distance p q := by
    rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg ((embedding.point p).1 - (embedding.point q).1)]
  by_contra hSeparated
  have hDistance : embedding.distance p q < ell := lt_of_not_ge hSeparated
  rcases side with ⟨i, j, vertical⟩
  by_cases hVertical : vertical
  · have hqBounds := hq
    simp [daiLiGridSideStripQubits, hVertical] at hqBounds
    have hQLine : |(embedding.point q).1 -
        ((gridOrigin w t).1 + (i : ℝ) * w)| ≤ ell := by
      rw [abs_le]
      constructor <;> linarith [hqBounds.1.1, hqBounds.1.2]
    have hPLine : |(embedding.point p).1 -
        ((gridOrigin w t).1 + (i : ℝ) * w)| ≤ 2 * ell := by
      calc
        |(embedding.point p).1 - ((gridOrigin w t).1 + (i : ℝ) * w)| =
            |((embedding.point p).1 - (embedding.point q).1) +
              ((embedding.point q).1 - ((gridOrigin w t).1 + (i : ℝ) * w))| := by
              congr 1
              ring
        _ ≤ |(embedding.point p).1 - (embedding.point q).1| +
              |(embedding.point q).1 - ((gridOrigin w t).1 + (i : ℝ) * w)| :=
            abs_add_le _ _
        _ ≤ ell + ell := by
            gcongr
            exact hCoordinateX.trans hDistance.le
        _ = 2 * ell := by ring
    apply hpNotEdge
    unfold edgeBad
    left
    have htX : t.1 = ((gridOrigin w t).1 : AddCircle w) := by
      have hPhase := congrArg Prod.fst (phase_gridOrigin w t)
      simpa [phase] using hPhase.symm
    rw [htX]
    have hperiod :
        (((gridOrigin w t).1 + (i : ℝ) * w : ℝ) : AddCircle w) =
          ((gridOrigin w t).1 : AddCircle w) :=
      addCircle_coe_add_int_mul_period w (gridOrigin w t).1 i
    have hdist := addCircle_dist_le_abs_sub w
      ((gridOrigin w t).1 + (i : ℝ) * w) (embedding.point p).1 hw
    rw [hperiod] at hdist
    calc
      dist ((gridOrigin w t).1 : AddCircle w) (phase w (embedding.point p)).1 ≤
          |(embedding.point p).1 - (gridOrigin w t).1 - (i : ℝ) * w| := by
        simp only [sub_add_eq_sub_sub] at hdist
        exact hdist
      _ = |(embedding.point p).1 - ((gridOrigin w t).1 + (i : ℝ) * w)| := by
        congr 1
        ring
      _ ≤ 2 * ell := hPLine
  · have hqBounds := hq
    simp [daiLiGridSideStripQubits, hVertical] at hqBounds
    have hQLine : |(embedding.point q).2 -
        ((gridOrigin w t).2 + (j : ℝ) * w)| ≤ ell := by
      rw [abs_le]
      constructor <;> linarith [hqBounds.2.1, hqBounds.2.2]
    have hPLine : |(embedding.point p).2 -
        ((gridOrigin w t).2 + (j : ℝ) * w)| ≤ 2 * ell := by
      calc
        |(embedding.point p).2 - ((gridOrigin w t).2 + (j : ℝ) * w)| =
            |((embedding.point p).2 - (embedding.point q).2) +
              ((embedding.point q).2 - ((gridOrigin w t).2 + (j : ℝ) * w))| := by
              congr 1
              ring
        _ ≤ |(embedding.point p).2 - (embedding.point q).2| +
              |(embedding.point q).2 - ((gridOrigin w t).2 + (j : ℝ) * w)| :=
            abs_add_le _ _
        _ ≤ ell + ell := by
            gcongr
            exact hCoordinateY.trans hDistance.le
        _ = 2 * ell := by ring
    apply hpNotEdge
    unfold edgeBad
    right
    have htY : t.2 = ((gridOrigin w t).2 : AddCircle w) := by
      have hPhase := congrArg Prod.snd (phase_gridOrigin w t)
      simpa [phase] using hPhase.symm
    rw [htY]
    have hperiod :
        (((gridOrigin w t).2 + (j : ℝ) * w : ℝ) : AddCircle w) =
          ((gridOrigin w t).2 : AddCircle w) :=
      addCircle_coe_add_int_mul_period w (gridOrigin w t).2 j
    have hdist := addCircle_dist_le_abs_sub w
      ((gridOrigin w t).2 + (j : ℝ) * w) (embedding.point p).2 hw
    rw [hperiod] at hdist
    calc
      dist ((gridOrigin w t).2 : AddCircle w) (phase w (embedding.point p)).2 ≤
          |(embedding.point p).2 - (gridOrigin w t).2 - (j : ℝ) * w| := by
        simp only [sub_add_eq_sub_sub] at hdist
        exact hdist
      _ = |(embedding.point p).2 - ((gridOrigin w t).2 + (j : ℝ) * w)| := by
        congr 1
        ring
      _ ≤ 2 * ell := hPLine
end QEC.Locality
