-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.toFiniteInstrument_inducedMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:00:45.854205+00:00
-- url     : https://prove2.me/submissions/c27d0a22-06dd-4cc9-8135-3325973eb96c

import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_inducedMap_eq

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
theorem _root_.solution (Φ : QuantumChannel H K)
    (A : Operator H) :
    (Φ.toFiniteInstrument).kraus.inducedMap A = Φ A := by
  exact LinearMap.congr_fun Φ.toFiniteInstrument_inducedMap_eq A
end QEC.Semantics.QuantumChannel
