-- Prove2me | solution 1 for QEC.Locality.exists_good_translation_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:44:41.646207+00:00
-- url     : https://prove2.me/submissions/39c16ed0-29eb-4beb-8b50-1f7cdb6c0447

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_vertexScore_eq_cast_count
import Theorems.Thm_QEC_Locality_edgeScore_eq_cast_count
import Theorems.Thm_QEC_Locality_integrable_vertexScore
import Theorems.Thm_QEC_Locality_integrable_edgeScore
import Theorems.Thm_QEC_Locality_average_vertexScore
import Theorems.Thm_QEC_Locality_average_edgeScore_le
import Theorems.Thm_QEC_Locality_average_const_mul_add
import Theorems.Thm_QEC_Locality_volume_gridTranslation_ne_zero
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
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
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
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
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution
    {a b : Type*} [Fintype a] [Fintype b] [Nonempty a] [Nonempty b]
    (w ell : ℝ) (hell : 0 < ell) (hscale : 4 * ell ≤ w)
    (X : a → ℝ × ℝ) (Y : b → ℝ × ℝ) :
    ∃ t : AddCircle w × AddCircle w,
      (vertexBadCount w (2 * ell) X t : ℝ) ≤
          (32 * ell ^ 2 / w ^ 2) * Fintype.card a ∧
        (edgeBadCount w (2 * ell) Y t : ℝ) ≤
          (16 * ell / w) * Fintype.card b := by
  have hw : 0 < w := lt_of_lt_of_le (by nlinarith [hell]) hscale
  letI : Fact (0 < w) := ⟨hw⟩
  let A : ℝ := Fintype.card a * (16 * ell ^ 2 / w ^ 2)
  let B : ℝ := Fintype.card b * (8 * ell / w)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  let score : AddCircle w × AddCircle w → ℝ := fun t =>
    B * vertexScore w (2 * ell) X t + A * edgeScore w (2 * ell) Y t
  have hvertexInt := integrable_vertexScore w (2 * ell) X
  have hedgeInt := integrable_edgeScore w (2 * ell) Y
  have hscoreInt : Integrable score volume :=
    (hvertexInt.const_mul B).add (hedgeInt.const_mul A)
  obtain ⟨t, ht⟩ := MeasureTheory.exists_le_average
    (volume_gridTranslation_ne_zero w) hscoreInt
  have havg : (⨍ s, score s ∂volume) ≤ 2 * A * B := by
    rw [show (⨍ s, score s ∂volume) =
        B * (⨍ s, vertexScore w (2 * ell) X s ∂volume) +
          A * (⨍ s, edgeScore w (2 * ell) Y s ∂volume) by
      exact average_const_mul_add volume _ _ A B hvertexInt hedgeInt]
    rw [average_vertexScore w ell hell.le hscale X]
    have hedgeAvg := average_edgeScore_le w ell hell.le hscale Y
    dsimp [A, B]
    nlinarith
  have hscore : score t ≤ 2 * A * B := ht.trans havg
  have hvnonneg : 0 ≤ vertexScore w (2 * ell) X t := by
    rw [vertexScore_eq_cast_count]
    positivity
  have henonneg : 0 ≤ edgeScore w (2 * ell) Y t := by
    rw [edgeScore_eq_cast_count]
    positivity
  have hv : vertexScore w (2 * ell) X t ≤ 2 * A := by
    dsimp [score] at hscore
    nlinarith
  have he : edgeScore w (2 * ell) Y t ≤ 2 * B := by
    dsimp [score] at hscore
    nlinarith
  refine ⟨t, ?_, ?_⟩
  · rw [← vertexScore_eq_cast_count]
    calc
      _ ≤ 2 * A := hv
      _ = _ := by dsimp [A]; ring
  · rw [← edgeScore_eq_cast_count]
    calc
      _ ≤ 2 * B := he
      _ = _ := by dsimp [B]; ring
end QEC.Locality
