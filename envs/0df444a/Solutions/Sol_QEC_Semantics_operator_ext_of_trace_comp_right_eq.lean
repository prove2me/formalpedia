-- Prove2me | solution 1 for QEC.Semantics.operator_ext_of_trace_comp_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:18:42.361557+00:00
-- url     : https://prove2.me/submissions/cf75ddef-e257-484a-8b1c-23ed5f3223a9

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution {S T : Operator H}
    (htrace : ∀ A : Operator H,
      LinearMap.trace Complex H (A.comp S) = LinearMap.trace Complex H (A.comp T)) :
    S = T := by
  classical
  let b := Module.Free.chooseBasis Complex H
  apply (LinearMap.toMatrix b b).injective
  apply (Matrix.ext_iff_trace_mul_left).2
  intro X
  let A : Operator H := Matrix.toLin b b X
  have hA := htrace A
  rw [LinearMap.trace_eq_matrix_trace Complex b, LinearMap.trace_eq_matrix_trace Complex b] at hA
  rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b] at hA
  simpa [A] using hA
end QEC.Semantics
