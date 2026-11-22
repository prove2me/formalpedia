-- Prove2me | solution 1 for computation_is_linearisation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:40.12079+00:00
-- url     : https://prove2.me/submissions/42678e9b-7cd7-43a1-b8a6-83f9719dd758

import Definitions.Def_EventStructures_Family_Path
import Definitions.Def_EventStructures_Family_Trace
import Mathlib.Logic.Function.Basic
import Definitions.Def_EventStructures_Family_Computation

set_option autoImplicit true
variable {L : Type*} (F : ConfFamily L)
open ConfFamily Path Trace
theorem _root_.solution {c : Conf F} (comp : Computation F c) :
    ∃ t : List F.Event, isLinearisation F c t := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep comp
  exact ⟨Path.trace F p, ⟨p, .refl _⟩⟩
