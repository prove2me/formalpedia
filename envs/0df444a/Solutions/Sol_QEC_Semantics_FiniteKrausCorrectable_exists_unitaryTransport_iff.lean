-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausCorrectable.exists_unitaryTransport_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:43:11.497621+00:00
-- url     : https://prove2.me/submissions/d07e43a1-1fa9-41dc-8f07-9e5b280803ef

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_FiniteKrausCorrectable_of_unitaryTransport
import Theorems.Thm_QEC_Semantics_Correctable_of_unitaryTransport
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport


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
    {C : QuantumCode H} {noise : FiniteKrausFamily ι H K} :
    (∃ recovery : QuantumChannel Kt Ht,
      FiniteKrausCorrectable ι Ht Kt (C.transport U)
        (noise.unitaryTransport U V) recovery) ↔
    (∃ recovery : QuantumChannel K H,
      FiniteKrausCorrectable ι H K C noise recovery) := by
  constructor
  · rintro ⟨recovery, h⟩
    exact ⟨QuantumChannel.comp (QuantumChannel.unitaryConj U.symm)
      (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V)),
      of_unitaryTransport U V h⟩
  · rintro ⟨recovery, h⟩
    exact ⟨QuantumChannel.comp (QuantumChannel.unitaryConj U)
      (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V.symm)),
      unitaryTransport U V h⟩
end QEC.Semantics.FiniteKrausCorrectable
