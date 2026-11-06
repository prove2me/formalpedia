-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.fixedDensityReplacementSwap_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:50:57.564911+00:00
-- url     : https://prove2.me/submissions/a208e738-85ec-4e88-a347-461c752a38aa

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel

set_option autoImplicit false
universe v w
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h : H) (k : K) :
    fixedDensityReplacementSwap H K (h ⊗ₜ[Complex] k) = k ⊗ₜ[Complex] h :=
  rfl
end QEC.Semantics.FiniteInstrument
