-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.traceNorm_density_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:38:29.817106+00:00
-- url     : https://prove2.me/submissions/65bf4ade-8218-4542-ac3e-dc21a6cbe2ad

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Theorems.Thm_QEC_Semantics_QuantumChannel_traceNorm_apply_le_of_isSymmetric
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
theorem _root_.solution [Nontrivial H] [Nontrivial K]
    (Phi : QuantumChannel H K) (rho sigma : DensityOperator H) :
    traceNorm (Phi rho.toOperator - Phi sigma.toOperator) ≤
      traceNorm (rho.toOperator - sigma.toOperator) := by
  have hsym : (rho.toOperator - sigma.toOperator).IsSymmetric :=
    rho.positive.isSymmetric.sub sigma.positive.isSymmetric
  simpa [map_sub] using
    Phi.traceNorm_apply_le_of_isSymmetric (rho.toOperator - sigma.toOperator) hsym
end QEC.Semantics.QuantumChannel
