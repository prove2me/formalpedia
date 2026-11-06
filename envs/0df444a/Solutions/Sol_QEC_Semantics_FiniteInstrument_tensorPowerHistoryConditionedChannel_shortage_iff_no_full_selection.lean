-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedChannel_shortage_iff_no_full_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:22:10.338194+00:00
-- url     : https://prove2.me/submissions/e00e66ac-6563-436d-8cb5-fdac89142ab1

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAccepted_shortage_iff_no_full_selection


set_option autoImplicit false
universe v w
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts) (required : Nat) :
    (tensorPowerAcceptedIndices accepts attempts history).card < required ↔
      ¬ ∃ selection : Fin required → Fin attempts,
        Function.Injective selection ∧
          ∀ slot, selection slot ∈ tensorPowerAcceptedIndices accepts attempts history :=
  tensorPowerAccepted_shortage_iff_no_full_selection accepts attempts history required
end QEC.Semantics.FiniteInstrument
