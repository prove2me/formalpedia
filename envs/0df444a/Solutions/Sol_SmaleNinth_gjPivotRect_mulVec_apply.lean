-- Prove2me | solution 1 for SmaleNinth.gjPivotRect_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T08:27:00.381824+00:00
-- url     : https://prove2.me/submissions/225dfe93-dfdd-48dc-bb96-177d9e6276b3

import Definitions.Def_SmaleNinth_GaussJordanPlus
import Theorems.Thm_SmaleNinth_div_row_dotProduct

open Matrix SmaleNinth

theorem solution {r c : ℕ}
    (S : Matrix (Fin r) (Fin c) ℝ) (i : Fin r) (j : Fin c)
    (z : Fin c → ℝ) (a : Fin r) :
    (SmaleNinth.gjPivotRect S i j).mulVec z a =
      if a = i then
        S.mulVec z a / S i j
      else
        S.mulVec z a - S a j * (S.mulVec z i) / S i j := by
  by_cases hai : a = i
  · subst a
    simp only [SmaleNinth.gjPivotRect, ↓reduceIte, Matrix.mulVec]
    exact SmaleNinth.div_row_dotProduct (S i) z (S i j)
  · simp only [SmaleNinth.gjPivotRect, hai, ↓reduceIte, Matrix.mulVec]
    have hrow :
        (fun k => S a k - S a j * (S i k / S i j)) =
          S a - (fun k => S a j * (S i k / S i j)) := by
      funext k
      simp
    have hscale :
        ((fun k => S a j * (S i k / S i j)) ⬝ᵥ z) =
          S a j * (((fun k => S i k / S i j) ⬝ᵥ z)) := by
      rw [← smul_eq_mul]
      exact smul_dotProduct (S a j) (fun k => S i k / S i j) z
    rw [hrow, sub_dotProduct, hscale]
    rw [SmaleNinth.div_row_dotProduct]
    ring
