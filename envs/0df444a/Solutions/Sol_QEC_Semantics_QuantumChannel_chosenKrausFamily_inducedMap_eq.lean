-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.chosenKrausFamily_inducedMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:15.812196+00:00
-- url     : https://prove2.me/submissions/3f2386b2-6048-4907-ac72-87c1b6953712

import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Theorems.Thm_QEC_Semantics_QuantumChannel_chosenKrausFamily_representation

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
    (Φ.chosenKrausFamily).inducedMap = Φ.toLinearMap :=
  (Φ.chosenKrausFamily_representation).2
end QEC.Semantics.QuantumChannel
