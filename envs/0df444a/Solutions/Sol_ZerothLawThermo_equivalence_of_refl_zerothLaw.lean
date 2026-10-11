-- Prove2me | solution 1 for ZerothLawThermo.equivalence_of_refl_zerothLaw
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:42:44.370987+00:00
-- url     : https://prove2.me/submissions/799ba936-57e0-447b-926f-894411788e00

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem solution {S : Type*} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) (hzero : ZerothLaw TE) :
    Equivalence TE := by
  have hs : ∀ {A B : S}, TE A B → TE B A := fun {A B} h => hzero B A B (hrefl B) h
  exact ⟨hrefl, hs, fun hAB hBC => hzero _ _ _ hAB (hs hBC)⟩
