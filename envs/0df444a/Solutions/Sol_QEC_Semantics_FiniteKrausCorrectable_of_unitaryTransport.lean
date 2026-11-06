-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausCorrectable.of_unitaryTransport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:35:16.820759+00:00
-- url     : https://prove2.me/submissions/7469f25a-7d30-4fdb-98e8-b56e468b5ff2

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_of_unitaryTransport_complete
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_conjDensity_transport
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
open QEC.Semantics.FiniteKrausCorrectable
variable {ι : Type v} [Fintype ι]
variable {H K Ht Kt : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
variable [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
namespace QEC.Semantics.FiniteKrausCorrectable
theorem _root_.solution
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : FiniteKrausFamily ι H K}
    {recovery : QuantumChannel Kt Ht}
    (h : FiniteKrausCorrectable ι Ht Kt (C.transport U)
      (noise.unitaryTransport U V) recovery) :
    FiniteKrausCorrectable ι H K C noise
      (QuantumChannel.comp (QuantumChannel.unitaryConj U.symm)
        (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V))) := by
  rcases h with ⟨hcomplete, hcorrected⟩
  constructor
  · exact noise.of_unitaryTransport_complete U V hcomplete
  · intro rho hρ
    let rhoT : DensityOperator Ht := U.conjDensity rho
    have hρT : DensityOperator.SupportedOn (C.transport U) rhoT := by
      exact DensityOperator.supportedOn_conjDensity_transport U C rho hρ
    have hcorr := hcorrected rhoT hρT
    have hcorr' : recovery (V.conjOperator (noise.inducedMap rho.toOperator)) =
        U.conjOperator rho.toOperator := by
      rw [FiniteKrausFamily.unitaryTransport_inducedMap_apply] at hcorr
      simpa [rhoT] using hcorr
    change U.symm.conjOperator
        (recovery (V.conjOperator (noise.inducedMap rho.toOperator))) = rho.toOperator
    rw [hcorr']
    rw [UnitaryTransport.symm_conjOperator_conjOperator]
end QEC.Semantics.FiniteKrausCorrectable
