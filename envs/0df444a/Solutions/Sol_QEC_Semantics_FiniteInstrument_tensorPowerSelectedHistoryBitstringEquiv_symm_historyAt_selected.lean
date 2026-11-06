-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:09:12.900437+00:00
-- url     : https://prove2.me/submissions/eb7085f4-6e85-499b-b893-9c6e5120f847

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialComplement
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_symm_at_selected

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
    (slot : Fin required) :
    tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history required
          hrequired ι).symm (selected, complement))
        (tensorPowerAcceptedSelector accepts attempts history required hrequired slot) =
      fun port => selected (slot, port) := by
  funext port
  exact tensorPowerSelectedHistoryBitstringEquiv_symm_at_selected accepts attempts
    history required hrequired ι selected complement slot port
end QEC.Semantics.FiniteInstrument
