-- Prove2me | solution 1 for QEC.Semantics.Correctable.exists_unitaryTransport_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:32:45.719197+00:00
-- url     : https://prove2.me/submissions/934d8406-396b-4e1b-85d2-0a2da54e08f5

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Channels_Core
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
import Theorems.Thm_QEC_Semantics_Correctable_of_unitaryTransport

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
    {C : QuantumCode H} {noise : QuantumChannel H K} :
    (∃ recovery : QuantumChannel Kt Ht,
      Correctable Ht Kt (C.transport U)
        (QuantumChannel.comp (QuantumChannel.unitaryConj V)
          (QuantumChannel.comp noise (QuantumChannel.unitaryConj U.symm)))
        recovery) ↔
    (∃ recovery : QuantumChannel K H, Correctable H K C noise recovery) := by
  constructor
  · rintro ⟨recovery, h⟩
    exact ⟨QuantumChannel.comp (QuantumChannel.unitaryConj U.symm)
      (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V)),
      of_unitaryTransport U V h⟩
  · rintro ⟨recovery, h⟩
    exact ⟨QuantumChannel.comp (QuantumChannel.unitaryConj U)
      (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V.symm)),
      unitaryTransport U V h⟩
end QEC.Semantics.Correctable
