-- Prove2me | solution 1 for QEC.Semantics.Davies.dissipatorNorm_le_squareSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:14:27.638523+00:00
-- url     : https://prove2.me/submissions/201ee0b2-08fc-4e62-9c69-184ff8b7a467

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
import Theorems.Thm_QEC_Semantics_Davies_dissipator_traceNorm_le_squareSum
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_operatorNorm_nonneg
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



set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]
namespace QEC.Semantics.Davies
theorem _root_.solution (J : κ → Operator V) :
    lindbladDissipatorNorm J ≤ 2 * operatorNorm (squareSum J) := by
  apply csSup_le
  · refine ⟨0, 0, ?_, ?_, ?_⟩
    · intro x y; simp
    · rw [(traceNorm_eq_zero_iff _).mpr rfl]; norm_num
    · rw [map_zero, (traceNorm_eq_zero_iff _).mpr rfl]
  · rintro r ⟨F,hF,hFn,rfl⟩
    exact (dissipator_traceNorm_le_squareSum J F hF).trans
      (by nlinarith [operatorNorm_nonneg (squareSum J)])
end QEC.Semantics.Davies
