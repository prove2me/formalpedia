-- Prove2me | solution 1 for ZerothLawThermo.trans_of_refl_zerothLaw
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:42:50.353693+00:00
-- url     : https://prove2.me/submissions/bc771d1c-5158-44ea-81cf-68032fc83c69

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem solution {S : Type*} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) (hzero : ZerothLaw TE) (A B C : S)
    (hAB : TE A B) (hBC : TE B C) :
    TE A C := by
  exact hzero A C B hAB (hzero C B C (hrefl C) hBC)
