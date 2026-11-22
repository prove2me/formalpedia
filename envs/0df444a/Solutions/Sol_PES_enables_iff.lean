-- Prove2me | solution 1 for PES.enables_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:47:44.959183+00:00
-- url     : https://prove2.me/submissions/c635a328-fb4a-486d-af6d-8f89503649ae

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Theorems.Thm_Configuration_enables_extension
import Theorems.Thm_ConfFamily_enables_extension


set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
variable {L : Type*} (P : PES L)
namespace PES
theorem _root_.solution {c : Set P.Event} {e : P.Event} :
    P.toFamily.enables c e ↔ Configuration.enables P c e := by
  constructor
  · rintro ⟨hc, hext⟩
    refine ⟨hc, fun e' he' => hext.1 (Or.inr rfl) (Or.inl he'), ?_⟩
    intro x hx
    rcases hext.2 (Or.inr rfl : e ∈ c ∪ {e}) (le_of_lt hx) with h | h
    · exact h
    · subst h
      exact absurd hx (lt_irrefl _)
  · exact fun h => ⟨h.1, Configuration.enables_extension P h⟩
end PES
