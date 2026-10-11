-- Prove2me | solution 1 for ZerothLawThermo.existence_of_temperature
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:42:56.44533+00:00
-- url     : https://prove2.me/submissions/52b80dd7-04ae-4ef0-8197-9e9df7714f40

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

universe u

open ZerothLawThermo

theorem solution {S : Type u} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) (hzero : ZerothLaw TE) :
    ∃ (T : Type u) (t : S → T), IsEmpiricalTemperature TE t := by
  have hs : ∀ {A B : S}, TE A B → TE B A := fun {A B} h => hzero B A B (hrefl B) h
  have he : Equivalence TE := ⟨hrefl, hs, fun hAB hBC => hzero _ _ _ hAB (hs hBC)⟩
  let r : Setoid S := ⟨TE, he⟩
  refine ⟨Quotient r, Quotient.mk r, ?_⟩
  intro A B
  exact ⟨fun h => Quotient.sound (s := r) h, fun h => Quotient.exact (s := r) h⟩
