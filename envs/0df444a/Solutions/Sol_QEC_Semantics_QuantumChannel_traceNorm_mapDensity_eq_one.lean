-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.traceNorm_mapDensity_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:50:23.989058+00:00
-- url     : https://prove2.me/submissions/a2ab82d3-0977-408a-8b01-615960f0ef27

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Theorems.Thm_QEC_Semantics_DensityOperator_traceNorm_eq_one
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
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
theorem _root_.solution [Nontrivial K]
    (Phi : QuantumChannel H K) (rho : DensityOperator H) :
    traceNorm (Phi rho.toOperator) = 1 := by
  simpa using (Phi.mapDensity rho).traceNorm_eq_one
end QEC.Semantics.QuantumChannel
