-- Prove2me | solution 1 for QEC.Semantics.Correctable.of_unitaryTransport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:54:04.338248+00:00
-- url     : https://prove2.me/submissions/1dad9fa9-808f-4ecf-bb06-91ab76c341d8

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Channels_Core
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_conjDensity_transport
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
open QEC.Semantics.Correctable
variable {H K Ht Kt : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
variable [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
namespace QEC.Semantics.Correctable
theorem _root_.solution
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : QuantumChannel H K}
    {recovery : QuantumChannel Kt Ht}
    (h : Correctable Ht Kt (C.transport U)
      (QuantumChannel.comp (QuantumChannel.unitaryConj V)
        (QuantumChannel.comp noise (QuantumChannel.unitaryConj U.symm)))
      recovery) :
    Correctable H K C noise
      (QuantumChannel.comp (QuantumChannel.unitaryConj U.symm)
        (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V))) := by
  intro rho hρ
  let rhoT : DensityOperator Ht := U.conjDensity rho
  have hρT : DensityOperator.SupportedOn (C.transport U) rhoT := by
    exact DensityOperator.supportedOn_conjDensity_transport U C rho hρ
  have hcorr := h rhoT hρT
  have hcorr' : recovery (V.conjOperator (noise rho.toOperator)) =
      U.conjOperator rho.toOperator := by
    simpa [rhoT] using hcorr
  change U.symm.conjOperator (recovery (V.conjOperator (noise rho.toOperator))) =
    rho.toOperator
  rw [hcorr']
  rw [UnitaryTransport.symm_conjOperator_conjOperator]
end QEC.Semantics.Correctable
