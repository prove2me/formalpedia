-- Prove2me | solution 1 for QEC.Locality.average_edge_indicator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:38:22.399474+00:00
-- url     : https://prove2.me/submissions/acaccb8a-8416-4f4b-81d7-c4c24ac90b28

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_measurableSet_edgeBad
import Theorems.Thm_QEC_Locality_measure_edgeBad_le
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
theorem _root_.solution (w ell : ℝ) [Fact (0 < w)]
    (hell : 0 ≤ ell) (hscale : 4 * ell ≤ w) (p : ℝ × ℝ) :
    (⨍ t : AddCircle w × AddCircle w,
      (if edgeBad w (2 * ell) t p then (1 : ℝ) else 0) ∂volume) ≤
      8 * ell / w := by
  classical
  have hmin : min w (2 * (2 * ell)) = 4 * ell := by
    rw [min_eq_right] <;> linarith
  have hind : (fun t : AddCircle w × AddCircle w =>
      if edgeBad w (2 * ell) t p then (1 : ℝ) else 0) =
      {t | edgeBad w (2 * ell) t p}.indicator 1 := by
    funext t
    by_cases h : edgeBad w (2 * ell) t p <;> simp [Set.indicator, h]
  rw [hind, MeasureTheory.average_eq,
    integral_indicator_one (measurableSet_edgeBad w (2 * ell) p)]
  change (ENNReal.toReal (volume (Set.univ : Set (AddCircle w × AddCircle w))))⁻¹ *
    ENNReal.toReal (volume {t | edgeBad w (2 * ell) t p}) ≤ _
  have huniv : ENNReal.toReal (volume (Set.univ : Set (AddCircle w × AddCircle w))) =
      w * w := by
    rw [← Set.univ_prod_univ, MeasureTheory.Measure.volume_eq_prod,
      MeasureTheory.Measure.prod_prod, AddCircle.measure_univ]
    simp only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (le_of_lt (Fact.out : 0 < w))]
  rw [huniv]
  have hmeasure := measure_edgeBad_le w (2 * ell) p
  rw [hmin] at hmeasure
  have hfinite : 2 * (ENNReal.ofReal (4 * ell) * ENNReal.ofReal w) ≠
      (∞ : ENNReal) := by finiteness
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top volume _) hfinite).2 hmeasure
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * ell),
    ENNReal.toReal_ofReal (le_of_lt (Fact.out : 0 < w))] at hreal
  norm_num at hreal
  rw [show (w * w)⁻¹ *
      ENNReal.toReal (volume {t : AddCircle w × AddCircle w | edgeBad w (2 * ell) t p}) =
      ENNReal.toReal (volume {t : AddCircle w × AddCircle w | edgeBad w (2 * ell) t p}) /
        w ^ 2 by rw [div_eq_mul_inv, pow_two, mul_comm]]
  rw [show 8 * ell / w = (8 * ell * w) / w ^ 2 by field_simp]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos (Fact.out : 0 < w))).2
  calc
    ENNReal.toReal (volume {t : AddCircle w × AddCircle w | edgeBad w (2 * ell) t p})
        ≤ 2 * (4 * ell * w) := hreal
    _ = 8 * ell * w := by ring
end QEC.Locality
