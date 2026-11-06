-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_observe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:22:21.583406+00:00
-- url     : https://prove2.me/submissions/7d019dfb-ce10-481e-a56c-5117e6ea0d0f

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_observe


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
    (firstIndex : tensorPowerHistory κ attempts)
    (secondIndex : Fin
      ((tensorPowerHistoryConditionedChannel accepts attempts
        ((I.tensorPower attempts).observe firstIndex) required ι shortageState).chosenKrausCount)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState).observe
      ⟨firstIndex, secondIndex⟩ =
        ⟨(I.tensorPower attempts).observe firstIndex, PUnit.unit⟩ := by
  change
    ((I.tensorPower attempts).bindDependent
      (fun history =>
        QuantumChannel.toFiniteInstrument
          (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))).observe
        ⟨firstIndex, secondIndex⟩ =
      ⟨(I.tensorPower attempts).observe firstIndex, PUnit.unit⟩
  exact FiniteInstrument.bindDependent_observe
    (I.tensorPower attempts)
    (fun history =>
      QuantumChannel.toFiniteInstrument
        (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))
    firstIndex secondIndex
end QEC.Semantics.FiniteInstrument
