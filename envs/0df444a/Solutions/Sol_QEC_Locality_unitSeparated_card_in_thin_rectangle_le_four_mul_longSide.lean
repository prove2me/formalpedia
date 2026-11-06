-- Prove2me | solution 1 for QEC.Locality.unitSeparated_card_in_thin_rectangle_le_four_mul_longSide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:08:10.973806+00:00
-- url     : https://prove2.me/submissions/1f46a76e-0bb8-422c-a93a-c55f40571469

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
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
    (embedding : UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.1 - lower.1)
    (hthin0 : 0 ≤ upper.2 - lower.2) (hthin1 : upper.2 - lower.2 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 4 * (upper.1 - lower.1) := by
  let width := upper.1 - lower.1
  let height := upper.2 - lower.2
  let xmid := (lower.1 + upper.1) / 2
  let ymid := (lower.2 + upper.2) / 2
  have hheight0 : 0 ≤ height := by simpa [height] using hthin0
  have eq_of_close
      (p q : i) (hxabs : |(embedding.point p).1 - (embedding.point q).1| < 3 / 4)
      (hyabs : |(embedding.point p).2 - (embedding.point q).2| < 1 / 2) : p = q := by
    by_contra hpq
    have hsep := embedding.unitSeparated hpq
    rw [euclideanDistance2D] at hsep
    have hxnonneg : 0 ≤ |(embedding.point p).1 - (embedding.point q).1| := abs_nonneg _
    have hynonneg : 0 ≤ |(embedding.point p).2 - (embedding.point q).2| := abs_nonneg _
    have hsumnonneg : 0 ≤ ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by positivity
    have hsqrt := Real.sq_sqrt hsumnonneg
    have hsqrt0 := Real.sqrt_nonneg (((embedding.point p).1 - (embedding.point q).1) ^ 2 +
        ((embedding.point p).2 - (embedding.point q).2) ^ 2)
    have hx2 : ((embedding.point p).1 - (embedding.point q).1) ^ 2 < 9 / 16 := by
      rw [← sq_abs]
      nlinarith
    have hy2 : ((embedding.point p).2 - (embedding.point q).2) ^ 2 < 1 / 4 := by
      rw [← sq_abs]
      nlinarith
    nlinarith
  by_cases hwidth : width < 3 / 2
  · let code : {p // p ∈ s} → Bool × Bool := fun p =>
      (decide ((embedding.point p.1).1 < xmid), decide ((embedding.point p.1).2 < ymid))
    have hcode : Function.Injective code := by
      intro p q hpq
      apply Subtype.ext
      apply eq_of_close p.1 q.1
      · have hpR := hmem p.1 p.2
        have hqR := hmem q.1 q.2
        rcases hpR with ⟨⟨hplx, hpux⟩, _⟩
        rcases hqR with ⟨⟨hqlx, hqux⟩, _⟩
        have hxCode := congrArg Prod.fst hpq
        have hxabs : |(embedding.point p.1).1 - (embedding.point q.1).1| ≤ width / 2 := by
          by_cases hpx : (embedding.point p.1).1 < xmid
          · have hqx : (embedding.point q.1).1 < xmid := by
              simpa [code, hpx] using hxCode
            rw [abs_le]
            constructor <;> dsimp [width, xmid] at * <;> linarith
          · have hqx : ¬ (embedding.point q.1).1 < xmid := by
              simpa [code, hpx] using hxCode
            rw [abs_le]
            constructor <;> dsimp [width, xmid] at * <;> linarith
        linarith
      · have hpR := hmem p.1 p.2
        have hqR := hmem q.1 q.2
        rcases hpR with ⟨_, ⟨hply, hpuy⟩⟩
        rcases hqR with ⟨_, ⟨hqly, hquy⟩⟩
        have hyCode := congrArg Prod.snd hpq
        have hyabs : |(embedding.point p.1).2 - (embedding.point q.1).2| ≤ height / 2 := by
          by_cases hpy : (embedding.point p.1).2 < ymid
          · have hqy : (embedding.point q.1).2 < ymid := by
              simpa [code, hpy] using hyCode
            rw [abs_le]
            constructor <;> dsimp [height, ymid] at * <;> linarith
          · have hqy : ¬ (embedding.point q.1).2 < ymid := by
              simpa [code, hpy] using hyCode
            rw [abs_le]
            constructor <;> dsimp [height, ymid] at * <;> linarith
        dsimp [height] at hyabs
        nlinarith [hheight0]
    have hcard := Fintype.card_le_of_injective code hcode
    have hs4 : s.card ≤ 4 := by simpa [code] using hcard
    have hs4R : (s.card : ℝ) ≤ 4 := by exact_mod_cast hs4
    dsimp [width] at hwidth ⊢
    nlinarith
  · let bins := Nat.floor (4 * width / 3) + 1
    let code : {p // p ∈ s} → Fin bins × Bool := fun p =>
      (⟨Nat.floor (4 * ((embedding.point p.1).1 - lower.1) / 3), by
          apply Nat.lt_succ_of_le
          apply Nat.floor_mono
          have hpR := hmem p.1 p.2
          rcases hpR with ⟨⟨_, hpux⟩, _⟩
          dsimp [width]
          linarith⟩,
        decide ((embedding.point p.1).2 < ymid))
    have hcode : Function.Injective code := by
      intro p q hpq
      apply Subtype.ext
      apply eq_of_close p.1 q.1
      · have hxCode :
            Nat.floor (4 * ((embedding.point p.1).1 - lower.1) / 3) =
              Nat.floor (4 * ((embedding.point q.1).1 - lower.1) / 3) := by
          have := congrArg (fun z => z.1.val) hpq
          simpa [code] using this
        have hpR := hmem p.1 p.2
        have hqR := hmem q.1 q.2
        rcases hpR with ⟨⟨hplx, _⟩, _⟩
        rcases hqR with ⟨⟨hqlx, _⟩, _⟩
        have hpFloor := Nat.floor_le
          (show 0 ≤ 4 * ((embedding.point p.1).1 - lower.1) / 3 by positivity)
        have hqFloor := Nat.floor_le
          (show 0 ≤ 4 * ((embedding.point q.1).1 - lower.1) / 3 by positivity)
        have hpNext := Nat.lt_floor_add_one
          (4 * ((embedding.point p.1).1 - lower.1) / 3)
        have hqNext := Nat.lt_floor_add_one
          (4 * ((embedding.point q.1).1 - lower.1) / 3)
        rw [hxCode] at hpFloor hpNext
        rw [abs_lt]
        constructor <;> norm_num at hpFloor hqFloor hpNext hqNext ⊢ <;> linarith
      · have hpR := hmem p.1 p.2
        have hqR := hmem q.1 q.2
        rcases hpR with ⟨_, ⟨hply, hpuy⟩⟩
        rcases hqR with ⟨_, ⟨hqly, hquy⟩⟩
        have hyCode : decide ((embedding.point p.1).2 < ymid) =
            decide ((embedding.point q.1).2 < ymid) := by
          have := congrArg Prod.snd hpq
          simpa [code] using this
        have hyabs : |(embedding.point p.1).2 - (embedding.point q.1).2| ≤ height / 2 := by
          by_cases hpy : (embedding.point p.1).2 < ymid
          · have hqy : (embedding.point q.1).2 < ymid := by
              simpa [hpy] using hyCode
            rw [abs_le]
            constructor <;> dsimp [height, ymid] at * <;> linarith
          · have hqy : ¬ (embedding.point q.1).2 < ymid := by
              simpa [hpy] using hyCode
            rw [abs_le]
            constructor <;> dsimp [height, ymid] at * <;> linarith
        dsimp [height] at hyabs
        nlinarith [hheight0]
    have hcard := Fintype.card_le_of_injective code hcode
    have hcard' : s.card ≤ 2 * (Nat.floor (4 * width / 3) + 1) := by
      simpa [code, bins, Nat.mul_comm] using hcard
    have hcardR : (s.card : ℝ) ≤ 2 * ((Nat.floor (4 * width / 3) : ℝ) + 1) := by
      exact_mod_cast hcard'
    have hfloor : (Nat.floor (4 * width / 3) : ℝ) ≤ 4 * width / 3 := by
      apply Nat.floor_le
      have : (0 : ℝ) ≤ width := by linarith [hlong]
      positivity
    dsimp [width] at hwidth hcardR hfloor ⊢
    nlinarith
end QEC.Locality
