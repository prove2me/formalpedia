-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:11:57.794617+00:00
-- url     : https://prove2.me/submissions/fc1949f2-b59e-4cb9-9320-068343c39173

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)) :
    tensorPowerSelectedPartialTraceChannel accepts attempts history required hrequired ι A =
      (tensorPowerSelectedRegisterReindex accepts attempts history required hrequired ι).conjOperator
        ((tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).selectedPartialTraceFromRegister
          ((tensorPowerQubitRegisterTransport ι attempts).conjOperator A)) :=
  rfl
end QEC.Semantics.FiniteInstrument
