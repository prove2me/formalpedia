-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptionalVertices_card_bound_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:41:50.97043+00:00
-- url     : https://prove2.me/submissions/b37ddb0f-7967-43fb-8d65-0edb91214b6c

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exceptionalVertices_card_bound_of_mixing
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
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
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
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



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (Delta : Nat) (epsilon : ℝ)
    (hDelta : 0 < Delta) (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hMixing : HasExpanderMixingBound (X.squareGraph side) (Delta * Delta)
      (4 * (Delta : ℝ)))
    (hSmall : ((X.activeVerticesOnSide side x).card : ℝ) ≤
      Fintype.card G / (4 * (Delta : ℝ) ^ (1 / 2 + epsilon))) :
    ((X.exceptionalVerticesOnSide side x
      (Nat.ceil ((Delta : ℝ) ^ (3 / 2 - epsilon)))).card : ℝ) ≤
      64 / (Delta : ℝ) ^ (1 - 2 * epsilon) *
        (X.activeVerticesOnSide side x).card := by
  have hD : (0 : ℝ) < Delta := by exact_mod_cast hDelta
  have hT : 0 < (Delta : ℝ) ^ (3 / 2 - epsilon) := Real.rpow_pos_of_pos hD _
  have hProduct : (Delta : ℝ) ^ (3 / 2 - epsilon) *
      (Delta : ℝ) ^ (1 / 2 + epsilon) = (Delta : ℝ) ^ 2 := by
    rw [← Real.rpow_add hD, show (3 / 2 - epsilon) + (1 / 2 + epsilon) =
      (2 : ℝ) by ring]
    norm_num
  have hDensity : 2 * ((Fintype.card A * Fintype.card B : Nat) : ℝ) *
      (X.activeVerticesOnSide side x).card ≤
      (Delta : ℝ) ^ (3 / 2 - epsilon) * Fintype.card G := by
    have hScaled := (le_div_iff₀ (by positivity :
      0 < 4 * (Delta : ℝ) ^ (1 / 2 + epsilon))).mp hSmall
    have hMult := mul_le_mul_of_nonneg_left hScaled hT.le
    rw [hA, hB, Nat.cast_mul]
    nlinarith [hProduct, (Nat.cast_nonneg (X.activeVerticesOnSide side x).card :
      (0 : ℝ) ≤ (X.activeVerticesOnSide side x).card)]
  have hBound := X.exceptionalVertices_card_bound_of_mixing side x
    (Nat.ceil ((Delta : ℝ) ^ (3 / 2 - epsilon)))
    ((Delta : ℝ) ^ (3 / 2 - epsilon)) (4 * (Delta : ℝ)) hT
    (Nat.le_ceil _) (by positivity) (by simpa [hA, hB] using hMixing) hDensity
  have hSquare : ((Delta : ℝ) ^ (3 / 2 - epsilon)) ^ 2 =
      (Delta : ℝ) ^ 2 * (Delta : ℝ) ^ (1 - 2 * epsilon) := by
    rw [← Real.rpow_mul_natCast hD.le, ← Real.rpow_natCast _ 2,
      ← Real.rpow_add hD]
    congr 1
    ring
  rw [hSquare] at hBound
  have hReduced : (Delta : ℝ) ^ (1 - 2 * epsilon) *
      (X.exceptionalVerticesOnSide side x
        (Nat.ceil ((Delta : ℝ) ^ (3 / 2 - epsilon)))).card ≤
      64 * (X.activeVerticesOnSide side x).card := by
    apply le_of_mul_le_mul_left (a := (Delta : ℝ) ^ 2) ?_ (by positivity)
    nlinarith [hBound]
  have hDen : 0 < (Delta : ℝ) ^ (1 - 2 * epsilon) := Real.rpow_pos_of_pos hD _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hDen).mpr
  nlinarith [hReduced]
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
