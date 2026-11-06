-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_unselected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:08:45.023698+00:00
-- url     : https://prove2.me/submissions/d65891ce-fdcf-4f47-b023-e06f2e0ff2bc

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialComplement
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_symm_at_unselected

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
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Qubit.Bitstring (Fin required × ι))
    (complement : Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired
        ι).ComplementCoordinates)
    (trial : tensorPowerUnselectedTrial accepts attempts history required hrequired) :
    tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history required
          hrequired ι).symm (selected, complement)) trial.1 =
      tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts history
        required hrequired ι complement trial := by
  funext port
  exact tensorPowerSelectedHistoryBitstringEquiv_symm_at_unselected accepts attempts
    history required hrequired ι selected complement trial port
end QEC.Semantics.FiniteInstrument
