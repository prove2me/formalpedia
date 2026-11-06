-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_branchOperator_of_enough
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:06:16.539199+00:00
-- url     : https://prove2.me/submissions/f9e98422-9858-4411-b296-d8520833967e

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedBranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_branchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedChannel_of_enough


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
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (A : Operator (tensorPowerCarrier H attempts)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required
        shortageState).branchOperator ⟨history, PUnit.unit⟩ A =
      tensorPowerSelectedPartialTraceChannel accepts attempts history required
        hrequired ι ((I.tensorPower attempts).branchOperator history A) := by
  rw [tensorPowerHistoryConditionedInstrument_branchOperator]
  rw [tensorPowerHistoryConditionedChannel_of_enough]
end QEC.Semantics.FiniteInstrument
