-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelector_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:30:37.946518+00:00
-- url     : https://prove2.me/submissions/b1cce642-9793-42b1-ab2c-bd12ed7b57a6

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (slot : Fin required) :
    tensorPowerAcceptedSelector accepts attempts history required hrequired slot ∈
      tensorPowerAcceptedIndices accepts attempts history :=
  Finset.orderEmbOfCardLe_mem _ _ _
end QEC.Semantics.FiniteInstrument
