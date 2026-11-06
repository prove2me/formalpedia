-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.toFiniteInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:58:45.444261+00:00
-- url     : https://prove2.me/submissions/3113fd22-38cb-4a7f-a77b-29e20843c588

import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Theorems.Thm_QEC_Semantics_QuantumChannel_chosenKrausFamily_complete

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
    (Φ.toFiniteInstrument).kraus.Complete :=
  Φ.chosenKrausFamily_complete
end QEC.Semantics.QuantumChannel
