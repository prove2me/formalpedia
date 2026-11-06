-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:34:47.213057+00:00
-- url     : https://prove2.me/submissions/02b521ed-c632-45aa-b0de-2538ec8951c0

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete


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
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (hI : I.kraus.Complete) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState).kraus.Complete := by
  change
    ((I.tensorPower attempts).bindDependent
      (fun history =>
        QuantumChannel.toFiniteInstrument
          (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))).kraus.Complete
  exact FiniteInstrument.bindDependent_complete
    (I.tensorPower attempts)
    (fun history =>
      QuantumChannel.toFiniteInstrument
        (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))
    (I.tensorPower_complete hI attempts)
    (fun history =>
      QuantumChannel.toFiniteInstrument_complete
        (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))
end QEC.Semantics.FiniteInstrument
