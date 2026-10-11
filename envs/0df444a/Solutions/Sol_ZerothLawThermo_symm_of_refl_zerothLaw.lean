-- Prove2me | solution 1 for ZerothLawThermo.symm_of_refl_zerothLaw
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:42:48.893962+00:00
-- url     : https://prove2.me/submissions/0735ff70-7f43-40dd-a33f-9a4dc81113a5

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem solution {S : Type*} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) (hzero : ZerothLaw TE) (A B : S) (hAB : TE A B) :
    TE B A := by
  exact hzero B A B (hrefl B) hAB
