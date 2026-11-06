-- Prove2me | solution 1 for QEC.Semantics.selfAdjointTraceNormOneToOne_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:32:17.189539+00:00
-- url     : https://prove2.me/submissions/c35e9995-4e03-4e08-b431-d8a7308ed252

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_eq_zero_iff
import Theorems.Thm_QEC_Semantics_traceNorm_neg
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
theorem _root_.solution (L : Superoperator H) :
    0 ≤ selfAdjointTraceNormOneToOne L := by
  apply le_csSup (selfAdjointTraceNormOneToOne_bddAbove L)
  refine ⟨(0 : Operator H), ?_, ?_, ?_⟩
  · intro x y
    simp
  · rw [(traceNorm_eq_zero_iff (0 : Operator H)).2 rfl]
    norm_num
  · rw [L.map_zero, (traceNorm_eq_zero_iff (0 : Operator H)).2 rfl]
end QEC.Semantics
