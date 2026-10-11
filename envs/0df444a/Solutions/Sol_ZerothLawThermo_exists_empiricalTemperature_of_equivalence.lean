-- Prove2me | solution 1 for ZerothLawThermo.exists_empiricalTemperature_of_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:42:54.725135+00:00
-- url     : https://prove2.me/submissions/f47ef595-368b-42d3-9cbd-bcb6aa845bb9

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

universe u

open ZerothLawThermo

theorem solution {S : Type u} (TE : S → S → Prop)
    (hTE : Equivalence TE) :
    ∃ (T : Type u) (t : S → T), IsEmpiricalTemperature TE t := by
  let r : Setoid S := ⟨TE, hTE⟩
  refine ⟨Quotient r, Quotient.mk r, ?_⟩
  intro A B
  exact ⟨fun h => Quotient.sound (s := r) h, fun h => Quotient.exact (s := r) h⟩
