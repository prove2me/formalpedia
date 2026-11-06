-- Prove2me | solution 1 for QEC.Semantics.traceNorm_apply_le_selfAdjointTraceNormOneToOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:40:11.657191+00:00
-- url     : https://prove2.me/submissions/88b720ff-60dc-4de5-a45f-78a3747d7141

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Theorems.Thm_QEC_Semantics_selfAdjointTraceNormOneToOne_nonneg
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_eq_zero_iff
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg
import Theorems.Thm_QEC_Semantics_traceNorm_smul
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


section
universe u v
namespace QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
private theorem traceNorm_apply_le_continuousNorm
    (L : Superoperator H) (A : Operator H) :
    traceNorm (L A) ≤ ‖traceNormContinuousSuperoperator L‖ * traceNorm A := by
  exact (traceNormContinuousSuperoperator L).le_opNorm A
private theorem selfAdjointTraceNormOneToOne_bddAbove (L : Superoperator H) :
    BddAbove {r : ℝ | ∃ A : Operator H,
      A.IsSymmetric ∧ traceNorm A ≤ 1 ∧ r = traceNorm (L A)} := by
  refine ⟨‖traceNormContinuousSuperoperator L‖, ?_⟩
  rintro r ⟨A, _hA, hnorm, rfl⟩
  calc
    traceNorm (L A) ≤ ‖traceNormContinuousSuperoperator L‖ * traceNorm A :=
      traceNorm_apply_le_continuousNorm L A
    _ ≤ ‖traceNormContinuousSuperoperator L‖ * 1 := by
      exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = ‖traceNormContinuousSuperoperator L‖ := mul_one _
end
end QEC.Semantics
end

set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution
    (L : Superoperator H) (A : Operator H) (hA : A.IsSymmetric) :
    traceNorm (L A) ≤ selfAdjointTraceNormOneToOne L * traceNorm A := by
  by_cases hzero : traceNorm A = 0
  · have hA0 : A = 0 := (traceNorm_eq_zero_iff A).1 hzero
    rw [hA0, L.map_zero, (traceNorm_eq_zero_iff (0 : Operator H)).2 rfl]
    exact mul_nonneg (selfAdjointTraceNormOneToOne_nonneg L) (le_refl 0)
  · have hpos : 0 < traceNorm A := lt_of_le_of_ne (traceNorm_nonneg A) (Ne.symm hzero)
    let c : ℂ := (traceNorm A : ℂ)⁻¹
    let B : Operator H := c • A
    have hBsym : B.IsSymmetric := by
      intro x y
      simp only [B, LinearMap.smul_apply, inner_smul_left, inner_smul_right]
      rw [hA x y]
      congr 1
      simp [c]
    have hc : ‖c‖ = (traceNorm A)⁻¹ := by
      simp [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hBnorm : traceNorm B ≤ 1 := by
      change traceNorm (c • A) ≤ 1
      rw [traceNorm_smul, hc, inv_mul_cancel₀ hzero]
    have hmember : traceNorm (L B) ∈ {r : ℝ | ∃ C : Operator H,
        C.IsSymmetric ∧ traceNorm C ≤ 1 ∧ r = traceNorm (L C)} :=
      ⟨B, hBsym, hBnorm, rfl⟩
    have hunit : traceNorm (L B) ≤ selfAdjointTraceNormOneToOne L :=
      le_csSup (selfAdjointTraceNormOneToOne_bddAbove L) hmember
    have hscale : L B = c • L A := by
      exact L.map_smul c A
    rw [hscale, traceNorm_smul] at hunit
    rw [hc] at hunit
    calc
      traceNorm (L A) = traceNorm A * ((traceNorm A)⁻¹ * traceNorm (L A)) := by
        field_simp
      _ ≤ traceNorm A * selfAdjointTraceNormOneToOne L :=
        mul_le_mul_of_nonneg_left hunit (traceNorm_nonneg A)
      _ = selfAdjointTraceNormOneToOne L * traceNorm A := mul_comm _ _
end QEC.Semantics
