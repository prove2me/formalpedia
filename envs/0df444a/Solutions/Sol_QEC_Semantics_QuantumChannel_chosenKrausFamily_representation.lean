-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.chosenKrausFamily_representation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:50:29.35683+00:00
-- url     : https://prove2.me/submissions/97095b0e-e21a-47a7-bdae-d4bc5c9d025f

import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Theorems.Thm_QEC_Semantics_QuantumChannel_exists_finiteKrausFamily_representation


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
    (Φ.chosenKrausFamily).Complete ∧
      (Φ.chosenKrausFamily).inducedMap = Φ.toLinearMap :=
  Classical.choose_spec
    (Classical.choose_spec Φ.exists_finiteKrausFamily_representation)
end QEC.Semantics.QuantumChannel
