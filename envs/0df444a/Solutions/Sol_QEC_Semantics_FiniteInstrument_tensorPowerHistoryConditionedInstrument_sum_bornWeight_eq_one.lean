-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_sum_bornWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:22:28.382616+00:00
-- url     : https://prove2.me/submissions/09dedbfd-006c-4e1c-9283-1d700adb8d37

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one


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
    (hI : I.kraus.Complete)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) :
    ∑ outcome,
      (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState).bornWeight
        outcome rho = 1 :=
  FiniteInstrument.sum_bornWeight_eq_one
    (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState)
    (tensorPowerHistoryConditionedInstrument_complete I accepts attempts required shortageState hI)
    rho
end QEC.Semantics.FiniteInstrument
