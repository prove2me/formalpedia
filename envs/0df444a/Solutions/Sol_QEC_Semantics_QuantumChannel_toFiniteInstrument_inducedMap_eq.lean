-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.toFiniteInstrument_inducedMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:58:50.255207+00:00
-- url     : https://prove2.me/submissions/49a159c4-dafe-4c3e-89fd-aac90f9a9a7c

import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Theorems.Thm_QEC_Semantics_QuantumChannel_chosenKrausFamily_inducedMap_eq

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
namespace QEC.Semantics.QuantumChannel
theorem _root_.solution (Φ : QuantumChannel H K) :
    (Φ.toFiniteInstrument).kraus.inducedMap = Φ.toLinearMap :=
  Φ.chosenKrausFamily_inducedMap_eq
end QEC.Semantics.QuantumChannel
