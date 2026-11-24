-- Prove2me | solution 1 for ULHC.bool_not_iff
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:09:06.710576+00:00
-- url     : https://prove2.me/submissions/800053db-30ea-4cf2-9c80-038c73495fd6

import Mathlib


theorem solution {p : Bool} {P : Prop} (h : p = true ↔ P) : (!p) = true ↔ ¬ P := by
  cases p <;> simp_all
