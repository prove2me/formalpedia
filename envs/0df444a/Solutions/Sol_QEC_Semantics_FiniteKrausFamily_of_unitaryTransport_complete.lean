-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.of_unitaryTransport_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:33:46.268443+00:00
-- url     : https://prove2.me/submissions/bda5e59e-328c-4031-8f22-be84020c3649

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
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
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    (hE : (E.unitaryTransport U V).Complete) :
    E.Complete := by
  have hback := (E.unitaryTransport U V).unitaryTransport_complete U.symm V.symm hE
  simpa only [Complete, unitaryTransport_symm_operator] using hback
end QEC.Semantics.FiniteKrausFamily
