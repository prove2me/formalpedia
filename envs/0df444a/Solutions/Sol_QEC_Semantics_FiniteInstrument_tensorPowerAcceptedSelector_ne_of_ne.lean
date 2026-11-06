-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerAcceptedSelector_ne_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:32:54.84543+00:00
-- url     : https://prove2.me/submissions/f095ba62-6d21-4e18-8645-312a45a0e7fe

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAcceptedSelector_injective

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
    {first second : Fin required} (hne : first ≠ second) :
    tensorPowerAcceptedSelector accepts attempts history required hrequired first ≠
      tensorPowerAcceptedSelector accepts attempts history required hrequired second :=
  (tensorPowerAcceptedSelector_injective accepts attempts history required hrequired).ne hne
end QEC.Semantics.FiniteInstrument
