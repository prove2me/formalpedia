-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.toFiniteInstrument_kraus
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:32:10.414769+00:00
-- url     : https://prove2.me/submissions/9897ff54-a630-4151-9c99-345b6f9529c9

import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
import Definitions.Def_QEC_Semantics_Channels_Instrument
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.QuantumChannel
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem solution (Φ : QuantumChannel H K) :
    (Φ.toFiniteInstrument).kraus = Φ.chosenKrausFamily := by
  rfl
