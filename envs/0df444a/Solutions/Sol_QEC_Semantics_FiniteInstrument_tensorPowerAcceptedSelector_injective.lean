-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelector_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:30:38.594834+00:00
-- url     : https://prove2.me/submissions/35f36d35-7d9d-4c40-baef-3783c41727b1

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
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card) :
    Function.Injective (tensorPowerAcceptedSelector accepts attempts history required hrequired) :=
  (tensorPowerAcceptedSelector accepts attempts history required hrequired).injective
end QEC.Semantics.FiniteInstrument
