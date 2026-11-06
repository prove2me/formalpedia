-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerSelectedCoordinateEmbedding_trials_ne_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:21:38.412581+00:00
-- url     : https://prove2.me/submissions/5197d0e8-01d0-4841-a28c-6ae39644e7e8

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAcceptedSelector_ne_of_ne


set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {first second : Fin required} (hne : first ≠ second) (port : ι) :
    (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
      (first, port)).1 ≠
      (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
        (second, port)).1 := by
  change tensorPowerAcceptedSelector accepts attempts history required hrequired first ≠
    tensorPowerAcceptedSelector accepts attempts history required hrequired second
  exact tensorPowerAcceptedSelector_ne_of_ne accepts attempts history required hrequired hne
end QEC.Semantics.FiniteInstrument
