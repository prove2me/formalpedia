-- Prove2me | solution 1 for ZerothLawThermo.zerothLaw_iff_zerothLawPlanck_of_refl
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:42:47.458785+00:00
-- url     : https://prove2.me/submissions/9bf648fb-d6d9-421b-9dd5-b4d811769b76

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem solution {S : Type*} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) :
    ZerothLaw TE ↔ ZerothLawPlanck TE := by
  constructor
  · intro hz A B C hCA hCB
    exact hz A B C (hz A C A (hrefl A) hCA) (hz B C B (hrefl B) hCB)
  · intro hz A B C hAC hBC
    exact hz A B C (hz C A A hAC (hrefl A)) (hz C B B hBC (hrefl B))
