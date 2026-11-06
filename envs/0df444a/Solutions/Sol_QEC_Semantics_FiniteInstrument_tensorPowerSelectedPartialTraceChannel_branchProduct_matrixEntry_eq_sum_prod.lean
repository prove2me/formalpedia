-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry_eq_sum_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:38:39.232945+00:00
-- url     : https://prove2.me/submissions/5cdcc46f-bd5a-4ff6-afd7-ca5c41e09c0b

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialProduct
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedBranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBranchOperatorMatrixEntryProduct_eq_prod


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
        inner Complex
            (tensorPowerBasis
              (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) 0 PUnit.unit)
            (unit
              (tensorPowerBasis
                (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) 0 PUnit.unit)) *
          ∏ trial : Fin attempts,
            inner Complex
              (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
                (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
                  ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts
                    observedHistory required hrequired ι).symm (left, complement))
                  trial))
              (branch (tensorPowerHistoryAt α attempts observedHistory trial)
                (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
                  (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
                    ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts
                      observedHistory required hrequired ι).symm (right, complement))
                    trial))) := by
  rw [tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry]
  apply Finset.sum_congr rfl
  intro complement _
  rw [tensorPowerBranchOperatorMatrixEntryProduct_eq_prod]
end QEC.Semantics.FiniteInstrument
