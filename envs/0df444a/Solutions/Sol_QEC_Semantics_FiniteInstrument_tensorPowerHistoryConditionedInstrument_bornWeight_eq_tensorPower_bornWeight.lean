-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_bornWeight_eq_tensorPower_bornWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:23:11.961006+00:00
-- url     : https://prove2.me/submissions/2f950a17-980b-4b75-af18-e311a181b024

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_bornWeight_punit
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete


set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (history : tensorPowerHistory Ω attempts)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState).bornWeight
        ⟨history, PUnit.unit⟩ rho =
      (I.tensorPower attempts).bornWeight history rho := by
  change
    ((I.tensorPower attempts).bindDependent
      (fun observedHistory => QuantumChannel.toFiniteInstrument
        (tensorPowerHistoryConditionedChannel accepts attempts observedHistory required ι
          shortageState))).bornWeight ⟨history, PUnit.unit⟩ rho =
      (I.tensorPower attempts).bornWeight history rho
  exact bindDependent_bornWeight_punit (I.tensorPower attempts)
    (fun observedHistory => QuantumChannel.toFiniteInstrument
      (tensorPowerHistoryConditionedChannel accepts attempts observedHistory required ι
        shortageState))
    (fun observedHistory => QuantumChannel.toFiniteInstrument_complete
      (tensorPowerHistoryConditionedChannel accepts attempts observedHistory required ι
        shortageState))
    history rho
end QEC.Semantics.FiniteInstrument
