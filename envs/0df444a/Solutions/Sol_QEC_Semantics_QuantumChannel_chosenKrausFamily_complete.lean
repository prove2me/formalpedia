-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.chosenKrausFamily_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:12.234016+00:00
-- url     : https://prove2.me/submissions/09ff7281-34c3-41ed-93f1-5380ba1cd816

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
    (Φ.chosenKrausFamily).Complete :=
  (Φ.chosenKrausFamily_representation).1
end QEC.Semantics.QuantumChannel
