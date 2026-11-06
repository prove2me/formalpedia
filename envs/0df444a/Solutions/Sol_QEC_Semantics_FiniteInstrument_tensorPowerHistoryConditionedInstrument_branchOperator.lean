-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_branchOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:03:01.190036+00:00
-- url     : https://prove2.me/submissions/5cba0cc2-ebcb-449f-89c1-7c7a9a993cc7

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedBranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_branchOperator_punit
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_inducedMap_apply


set_option autoImplicit false
universe v w
open QEC
open QEC.Semantics
open Classical
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
      [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (history : tensorPowerHistory Ω attempts)
    (A : Operator (tensorPowerCarrier H attempts)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required
        shortageState).branchOperator ⟨history, PUnit.unit⟩ A =
      tensorPowerHistoryConditionedChannel accepts attempts history required ι
        shortageState ((I.tensorPower attempts).branchOperator history A) := by
  change
    ((I.tensorPower attempts).bindDependent
      (fun observedHistory => QuantumChannel.toFiniteInstrument
        (tensorPowerHistoryConditionedChannel accepts attempts observedHistory
          required ι shortageState))).branchOperator
        ⟨history, PUnit.unit⟩ A = _
  rw [bindDependent_branchOperator_punit]
  exact QuantumChannel.toFiniteInstrument_inducedMap_apply
    (tensorPowerHistoryConditionedChannel accepts attempts history required ι
      shortageState) _
end QEC.Semantics.FiniteInstrument
