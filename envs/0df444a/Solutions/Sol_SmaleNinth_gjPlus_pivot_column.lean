-- Prove2me | solution 1 for SmaleNinth.gjPlus_pivot_column
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T16:03:08.717833+00:00
-- url     : https://prove2.me/submissions/3df154c8-1e54-4b64-be49-2821daab5d49

import Definitions.Def_SmaleNinth_GaussJordanPlus
import Mathlib.Tactic

open Matrix

theorem solution {s : ℕ} (S : Matrix (Fin s) (Fin s) ℝ) (j : Fin s)
    (h : S j j ≠ 0) :
    ∀ i : Fin s, SmaleNinth.gjPlus S j i j =
      if i = j then (1 / S j j) else -(S i j / S j j) := by
  intro i
  by_cases hi : i = j <;>
    simp [SmaleNinth.gjPlus, SmaleNinth.gjPivotRect, hi, h] <;>
    field_simp [h] <;>
    ring
