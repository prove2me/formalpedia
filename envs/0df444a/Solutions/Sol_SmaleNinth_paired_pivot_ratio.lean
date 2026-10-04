-- Prove2me | solution 1 for SmaleNinth.paired_pivot_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:24:47.174921+00:00
-- url     : https://prove2.me/submissions/f9434940-eddf-4698-a070-0584cd110721

import Mathlib
import Definitions.Def_SmaleNinth_GaussJordanPivot

open Matrix SmaleNinth in
theorem solution (S : Matrix (Fin 5) (Fin 5) ℝ)
    (hS : S.transpose = -S)
    (hq : S 0 4 ≠ 0)
    (ha : S 0 3 ≠ 0)
    (hd : S 3 4 - S 0 3 ≠ 0) :
    (pairedPivot5 S) 4 4 = 0 ∧
      S 0 3 * (pairedPivot5 S) 1 4 =
        (S 3 4 - S 0 3) * (pairedPivot5 S) 4 1 ∧
      S 0 3 * (pairedPivot5 S) 2 4 =
        (S 3 4 - S 0 3) * (pairedPivot5 S) 4 2 := by
  have hs : ∀ i j, S j i = - S i j := fun i j => by
    have := congrFun (congrFun hS i) j
    simpa [Matrix.transpose_apply] using this
  have h00 : S 0 0 = 0 := by linarith [hs 0 0]
  have h11 : S 1 1 = 0 := by linarith [hs 1 1]
  have h22 : S 2 2 = 0 := by linarith [hs 2 2]
  have h33 : S 3 3 = 0 := by linarith [hs 3 3]
  have h44 : S 4 4 = 0 := by linarith [hs 4 4]
  have h10 := hs 0 1
  have h20 := hs 0 2
  have h30 := hs 0 3
  have h40 := hs 0 4
  have h21 := hs 1 2
  have h31 := hs 1 3
  have h41 := hs 1 4
  have h32 := hs 2 3
  have h42 := hs 2 4
  have h43 := hs 3 4
  simp only [pairedPivot5, gjPivot, Matrix.updateRow_apply]
  simp only [Fin.isValue, Fin.reduceEq, if_false, if_true, h00, h11, h22, h33, h44,
    h10, h20, h30, h40, h21, h31, h41, h32, h42, h43]
  generalize S 0 1 = x01 at *
  generalize S 0 2 = x02 at *
  generalize S 0 3 = a at *
  generalize S 0 4 = q at *
  generalize S 1 2 = x12 at *
  generalize S 1 3 = x13 at *
  generalize S 1 4 = x14 at *
  generalize S 2 3 = x23 at *
  generalize S 2 4 = x24 at *
  generalize S 3 4 = x34 at *
  have e0 : ((0:ℝ) + -q) = -q := by ring
  have eD : ((0:ℝ) - -a * ((a + -x34) / -q)) = a * (x34 - a) / q := by
    field_simp; ring
  rw [e0]
  rw [eD]
  have hd' : x34 - a ≠ 0 := hd
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring
