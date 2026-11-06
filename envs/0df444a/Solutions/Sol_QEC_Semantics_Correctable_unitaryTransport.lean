-- Prove2me | solution 1 for QEC.Semantics.Correctable.unitaryTransport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:53:56.898205+00:00
-- url     : https://prove2.me/submissions/ff1cf112-1d54-4a55-aa1f-497421b91832

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Channels_Core
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_symm_conjDensity_transport_iff
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
    {recovery : QuantumChannel K H}
    (h : Correctable H K C noise recovery) :
    Correctable Ht Kt (C.transport U)
      (QuantumChannel.comp (QuantumChannel.unitaryConj V)
        (QuantumChannel.comp noise (QuantumChannel.unitaryConj U.symm)))
      (QuantumChannel.comp (QuantumChannel.unitaryConj U)
        (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V.symm))) := by
  intro rho hρ
  let rho₀ : DensityOperator H := U.symm.conjDensity rho
  have hρ₀ : DensityOperator.SupportedOn C rho₀ := by
    exact (DensityOperator.supportedOn_symm_conjDensity_transport_iff U C rho).2 hρ
  have hcorr := h rho₀ hρ₀
  have hcorr' : recovery (noise (U.symm.conjOperator rho.toOperator)) =
      U.symm.conjOperator rho.toOperator := by
    simpa [rho₀] using hcorr
  change U.conjOperator
      (recovery (V.symm.conjOperator
        (V.conjOperator (noise (U.symm.conjOperator rho.toOperator))))) =
    rho.toOperator
  rw [UnitaryTransport.symm_conjOperator_conjOperator]
  rw [hcorr']
  rw [UnitaryTransport.conjOperator_symm_conjOperator]
end QEC.Semantics.Correctable
