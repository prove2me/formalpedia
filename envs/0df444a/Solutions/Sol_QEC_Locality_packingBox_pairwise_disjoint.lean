-- Prove2me | solution 1 for QEC.Locality.packingBox_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:37:28.627669+00:00
-- url     : https://prove2.me/submissions/2dd5f03a-af2a-4ed0-8c21-bceeb8182197

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_two_mul_packingRadius
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
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i) :
    (s : Set i).PairwiseDisjoint (packingBox ∘ embedding.point) := by
  rw [Set.pairwiseDisjoint_iff]
  intro p hp q hq hpq
  by_contra hne
  obtain ⟨z, hzp, hzq⟩ := hpq
  have hpx : |(embedding.point p).1 - z.1| < packingRadius := by
    rcases hzp with ⟨⟨hzpl, hzpu⟩, _⟩
    rw [abs_lt]
    constructor <;> linarith
  have hqx : |z.1 - (embedding.point q).1| < packingRadius := by
    rcases hzq with ⟨⟨hzql, hzqu⟩, _⟩
    rw [abs_lt]
    constructor <;> linarith
  have hpy : |(embedding.point p).2 - z.2| < packingRadius := by
    rcases hzp with ⟨_, ⟨hzpl, hzpu⟩⟩
    rw [abs_lt]
    constructor <;> linarith
  have hqy : |z.2 - (embedding.point q).2| < packingRadius := by
    rcases hzq with ⟨_, ⟨hzql, hzqu⟩⟩
    rw [abs_lt]
    constructor <;> linarith
  have hx : |(embedding.point p).1 - (embedding.point q).1| < Real.sqrt 2 / 2 := by
    calc
      _ ≤ |(embedding.point p).1 - z.1| + |z.1 - (embedding.point q).1| := by
        simpa only [sub_add_sub_cancel] using
          abs_add_le ((embedding.point p).1 - z.1) (z.1 - (embedding.point q).1)
      _ < 2 * packingRadius := by linarith
      _ = _ := two_mul_packingRadius
  have hy : |(embedding.point p).2 - (embedding.point q).2| < Real.sqrt 2 / 2 := by
    calc
      _ ≤ |(embedding.point p).2 - z.2| + |z.2 - (embedding.point q).2| := by
        simpa only [sub_add_sub_cancel] using
          abs_add_le ((embedding.point p).2 - z.2) (z.2 - (embedding.point q).2)
      _ < 2 * packingRadius := by linarith
      _ = _ := two_mul_packingRadius
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx2 : ((embedding.point p).1 - (embedding.point q).1) ^ 2 < 1 / 2 := by
    rw [← sq_abs]
    have habs : 0 ≤ |(embedding.point p).1 - (embedding.point q).1| := abs_nonneg _
    have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith
  have hy2 : ((embedding.point p).2 - (embedding.point q).2) ^ 2 < 1 / 2 := by
    rw [← sq_abs]
    have habs : 0 ≤ |(embedding.point p).2 - (embedding.point q).2| := abs_nonneg _
    have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith
  have hsep := embedding.unitSeparated hne
  have hsum0 : 0 ≤ ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
      ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by positivity
  rw [QEC.Locality.euclideanDistance2D] at hsep
  nlinarith [Real.sq_sqrt hsum0]
end QEC.Locality
