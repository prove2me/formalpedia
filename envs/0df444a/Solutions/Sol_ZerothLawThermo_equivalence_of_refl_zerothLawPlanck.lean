-- Prove2me | solution 1 for ZerothLawThermo.equivalence_of_refl_zerothLawPlanck
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:42:45.979586+00:00
-- url     : https://prove2.me/submissions/79b8b68d-6700-44c4-b34f-ed06643d4be3

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem solution {S : Type*} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) (hzero : ZerothLawPlanck TE) :
    Equivalence TE := by
  have hs : ∀ {A B : S}, TE A B → TE B A := fun {A B} h => hzero B A A h (hrefl A)
  exact ⟨hrefl, hs, fun hAB hBC => hzero _ _ _ (hs hAB) hBC⟩
