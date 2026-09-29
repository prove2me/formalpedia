-- Prove2me | solution 1 for SmaleNinth.gjPlus_nonpivot_column
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T16:14:49.50447+00:00
-- url     : https://prove2.me/submissions/a0a01e7f-9990-4fe9-9ec1-9d50d73c5ffc

import Definitions.Def_SmaleNinth_GaussJordanPlus
import Mathlib.Tactic

open Matrix

theorem solution {s : ℕ} (S : Matrix (Fin s) (Fin s) ℝ) (j : Fin s)
    (h : S j j ≠ 0) {i q : Fin s} (hq : q ≠ j) :
    SmaleNinth.gjPlus S j i q =
      if i = j then S j q / S j j
      else S i q - S i j * (S j q / S j j) := by
  by_cases hi : i = j <;>
    simp [SmaleNinth.gjPlus, SmaleNinth.gjPivotRect, hi, hq, h] <;>
    field_simp [h] <;>
    ring
