-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_branchOperator_productInput_of_enough
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:37:12.384926+00:00
-- url     : https://prove2.me/submissions/6752f601-53cb-4857-ab26-edda0184f795

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedBranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_branchOperator_of_enough
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_tensorPower_productInput


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
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (history : tensorPowerHistory Ω attempts)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required
        shortageState).branchOperator ⟨history, PUnit.unit⟩
          (tensorPowerProductInput rho rhoUnit attempts).toOperator =
      tensorPowerSelectedPartialTraceChannel accepts attempts history required
        hrequired ι
        (tensorPowerBranchOperatorProduct
          (fun outcome => I.branchOperator outcome rho.toOperator)
          rhoUnit.toOperator attempts history) := by
  rw [tensorPowerHistoryConditionedInstrument_branchOperator_of_enough]
  rw [branchOperator_tensorPower_productInput]
end QEC.Semantics.FiniteInstrument
