-- Prove2me | solution 1 for QuantumMaxCutEnergy.tm2_of_polyprogram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:56:13.008808+00:00
-- url     : https://prove2.me/submissions/4d4d418a-65a4-427c-99ff-ec98fab8b57f

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

open OAI.MetricKMedian.Binary

theorem solution {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (P : PolyProgram ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
  ⟨P.stock⟩
