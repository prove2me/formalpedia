-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.traceNorm_apply_le_of_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:20:34.476626+00:00
-- url     : https://prove2.me/submissions/ea8e3289-f44e-4497-ad21-bd48aab74303

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_negativePart_positive
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_positivePart_positive
import Theorems.Thm_QEC_Semantics_positivePart_sub_negativePart
import Theorems.Thm_QEC_Semantics_traceNorm_add_le
import Theorems.Thm_QEC_Semantics_traceNorm_eq_re_trace_of_positive
import Theorems.Thm_QEC_Semantics_traceNorm_eq_sum_parts
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg



set_option autoImplicit false
universe u
open QEC QEC.Semantics
open scoped ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.QuantumChannel
variable {K L : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
namespace QEC.Semantics.QuantumChannel
theorem _root_.solution [Nontrivial H] [Nontrivial K]
    (Phi : QuantumChannel H K) (A : Operator H) (hA : A.IsSymmetric) :
    traceNorm (Phi A) ≤ traceNorm A := by
  have hdecomp := positivePart_sub_negativePart A hA
  calc
    traceNorm (Phi A) =
        traceNorm (Phi (positivePart A) - Phi (negativePart A)) := by
      rw [← map_sub, hdecomp]
    _ ≤ traceNorm (Phi (positivePart A)) + traceNorm (-Phi (negativePart A)) := by
      simpa [sub_eq_add_neg] using
        traceNorm_add_le (Phi (positivePart A)) (-Phi (negativePart A))
    _ = traceNorm (Phi (positivePart A)) + traceNorm (Phi (negativePart A)) := by
      rw [traceNorm_neg]
    _ = Complex.re (LinearMap.trace Complex K (Phi (positivePart A))) +
        Complex.re (LinearMap.trace Complex K (Phi (negativePart A))) := by
      rw [traceNorm_eq_re_trace_of_positive _
          (Phi.map_positive (positivePart_positive A)),
        traceNorm_eq_re_trace_of_positive _
          (Phi.map_positive (negativePart_positive A))]
    _ = Complex.re (LinearMap.trace Complex H (positivePart A)) +
        Complex.re (LinearMap.trace Complex H (negativePart A)) := by
      rw [Phi.trace_map, Phi.trace_map]
    _ = traceNorm (positivePart A) + traceNorm (negativePart A) := by
      rw [traceNorm_eq_re_trace_of_positive _ (positivePart_positive A),
        traceNorm_eq_re_trace_of_positive _ (negativePart_positive A)]
    _ = traceNorm A := (traceNorm_eq_sum_parts A hA).symm
end QEC.Semantics.QuantumChannel
