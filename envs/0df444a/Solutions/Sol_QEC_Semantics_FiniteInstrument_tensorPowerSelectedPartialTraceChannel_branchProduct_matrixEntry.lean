-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:36:36.996199+00:00
-- url     : https://prove2.me/submissions/7cbddd20-6597-4b64-ba2e-072a74cf6d25

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialProduct
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedBranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBranchOperatorProduct_matrixEntry
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_matrixEntry


set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (branch : α → Operator (Qubit.QubitRegister ι))
    (unit : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) 0))
    (left right : Qubit.Bitstring (Fin required × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex left)
        (tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
          required hrequired ι
          (tensorPowerBranchOperatorProduct branch unit attempts observedHistory)
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex right)) =
      ∑ complement : Qubit.Bitstring
          (tensorPowerSelectedSubsystem accepts attempts observedHistory required
            hrequired ι).ComplementCoordinates,
        tensorPowerBranchOperatorMatrixEntryProduct
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
          branch unit attempts observedHistory
          ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
            required hrequired ι).symm (left, complement))
          ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
            required hrequired ι).symm (right, complement)) := by
  rw [tensorPowerSelectedPartialTraceChannel_matrixEntry]
  apply Finset.sum_congr rfl
  intro complement _
  rw [tensorPowerBranchOperatorProduct_matrixEntry]
end QEC.Semantics.FiniteInstrument
