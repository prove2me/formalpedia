-- Prove2me | solution 1 for SmaleNinth.paired_pivot_ratio_qualified
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T14:02:45.393143+00:00
-- url     : https://prove2.me/submissions/4d10c92a-f209-4300-b583-cabff6dc8bc4

import Definitions.Def_SmaleNinth_GaussJordanPivot
import Mathlib.Tactic

open Matrix SmaleNinth

theorem solution (S : Matrix (Fin 5) (Fin 5) ℝ)
    (hS : S.transpose = -S)
    (hq : S 0 4 ≠ 0)
    (ha : S 0 3 ≠ 0)
    (hd : S 3 4 - S 0 3 ≠ 0) :
    (SmaleNinth.pairedPivot5 S) 4 4 = 0 ∧
      S 0 3 * (SmaleNinth.pairedPivot5 S) 1 4 =
        (S 3 4 - S 0 3) * (SmaleNinth.pairedPivot5 S) 4 1 ∧
      S 0 3 * (SmaleNinth.pairedPivot5 S) 2 4 =
        (S 3 4 - S 0 3) * (SmaleNinth.pairedPivot5 S) 4 2 := by
  let A : Matrix (Fin 5) (Fin 5) ℝ :=
    S.updateRow 0 (fun j => S 0 j + S 4 j)
  let B : Matrix (Fin 5) (Fin 5) ℝ := gjPivot A 0 0
  let C : Matrix (Fin 5) (Fin 5) ℝ := gjPivot B 3 3
  have hS' : ∀ i j : Fin 5, S j i = -S i j := by
    intro i j
    have h := congrArg
      (fun M : Matrix (Fin 5) (Fin 5) ℝ => M i j) hS
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  have hdiag (i : Fin 5) : S i i = 0 := by
    have hi := hS' i i
    linarith
  have hq' : (-S 0 4 : ℝ) ≠ 0 := by
    simpa [neg_eq_zero] using hq
  have A_ne (i j : Fin 5) (hi : i ≠ 0) : A i j = S i j := by
    dsimp [A]
    rw [Matrix.updateRow_apply]
    simp only [if_neg hi]
  have A0 (j : Fin 5) : A 0 j = S 0 j + S 4 j := by
    dsimp [A]
    rw [Matrix.updateRow_apply]
    simp
  have A00 : A 0 0 = -S 0 4 := by
    calc
      A 0 0 = S 0 0 + S 4 0 := A0 0
      _ = 0 + -S 0 4 := by rw [hdiag 0, hS' 0 4]
      _ = -S 0 4 := by ring
  have A01 : A 0 1 = S 0 1 - S 1 4 := by
    calc
      A 0 1 = S 0 1 + S 4 1 := A0 1
      _ = S 0 1 + -S 1 4 := by rw [hS' 1 4]
      _ = S 0 1 - S 1 4 := by ring
  have A02 : A 0 2 = S 0 2 - S 2 4 := by
    calc
      A 0 2 = S 0 2 + S 4 2 := A0 2
      _ = S 0 2 + -S 2 4 := by rw [hS' 2 4]
      _ = S 0 2 - S 2 4 := by ring
  have A03 : A 0 3 = S 0 3 - S 3 4 := by
    calc
      A 0 3 = S 0 3 + S 4 3 := A0 3
      _ = S 0 3 + -S 3 4 := by rw [hS' 3 4]
      _ = S 0 3 - S 3 4 := by ring
  have A04 : A 0 4 = S 0 4 := by
    calc
      A 0 4 = S 0 4 + S 4 4 := A0 4
      _ = S 0 4 + 0 := by rw [hdiag 4]
      _ = S 0 4 := by ring
  have A10 : A 1 0 = -S 0 1 := by
    calc A 1 0 = S 1 0 := A_ne 1 0 (by decide)
      _ = -S 0 1 := hS' 0 1
  have A13 : A 1 3 = S 1 3 := A_ne 1 3 (by decide)
  have A14 : A 1 4 = S 1 4 := A_ne 1 4 (by decide)
  have A20 : A 2 0 = -S 0 2 := by
    calc A 2 0 = S 2 0 := A_ne 2 0 (by decide)
      _ = -S 0 2 := hS' 0 2
  have A23 : A 2 3 = S 2 3 := A_ne 2 3 (by decide)
  have A24 : A 2 4 = S 2 4 := A_ne 2 4 (by decide)
  have A30 : A 3 0 = -S 0 3 := by
    calc A 3 0 = S 3 0 := A_ne 3 0 (by decide)
      _ = -S 0 3 := hS' 0 3
  have A31 : A 3 1 = -S 1 3 := by
    calc A 3 1 = S 3 1 := A_ne 3 1 (by decide)
      _ = -S 1 3 := hS' 1 3
  have A32 : A 3 2 = -S 2 3 := by
    calc A 3 2 = S 3 2 := A_ne 3 2 (by decide)
      _ = -S 2 3 := hS' 2 3
  have A33 : A 3 3 = 0 := by
    calc A 3 3 = S 3 3 := A_ne 3 3 (by decide)
      _ = 0 := hdiag 3
  have A34 : A 3 4 = S 3 4 := A_ne 3 4 (by decide)
  have A40 : A 4 0 = -S 0 4 := by
    calc A 4 0 = S 4 0 := A_ne 4 0 (by decide)
      _ = -S 0 4 := hS' 0 4
  have A41 : A 4 1 = -S 1 4 := by
    calc A 4 1 = S 4 1 := A_ne 4 1 (by decide)
      _ = -S 1 4 := hS' 1 4
  have A42 : A 4 2 = -S 2 4 := by
    calc A 4 2 = S 4 2 := A_ne 4 2 (by decide)
      _ = -S 2 4 := hS' 2 4
  have A43 : A 4 3 = -S 3 4 := by
    calc A 4 3 = S 4 3 := A_ne 4 3 (by decide)
      _ = -S 3 4 := hS' 3 4
  have A44 : A 4 4 = 0 := by
    calc A 4 4 = S 4 4 := A_ne 4 4 (by decide)
      _ = 0 := hdiag 4
  have B0 (j : Fin 5) : B 0 j = A 0 j / A 0 0 := by
    dsimp [B]
    simp [gjPivot]
  have B_raw (i j : Fin 5) (hi : i ≠ 0) :
      gjPivot A 0 0 i j =
        A i j - A i 0 * (A 0 j / A 0 0) := by
    simp [gjPivot, hi]
  have B_at (i j : Fin 5) (hi : i ≠ 0) :
      B i j = A i j - A i 0 * B 0 j := by
    calc
      B i j = gjPivot A 0 0 i j := by rfl
      _ = A i j - A i 0 * (A 0 j / A 0 0) := B_raw i j hi
      _ = A i j - A i 0 * B 0 j := by rw [B0]
  have B00 : B 0 0 = 1 := by
    rw [B0, A00]
    exact div_self hq'
  have B01 : B 0 1 = (S 1 4 - S 0 1) / S 0 4 := by
    rw [B0, A01, A00]
    field_simp [hq']
    ring
  have B02 : B 0 2 = (S 2 4 - S 0 2) / S 0 4 := by
    rw [B0, A02, A00]
    field_simp [hq']
    ring
  have B03 : B 0 3 = (S 3 4 - S 0 3) / S 0 4 := by
    rw [B0, A03, A00]
    field_simp [hq']
    ring
  have B04 : B 0 4 = -1 := by
    rw [B0, A04, A00]
    field_simp [hq']
  have B13 : B 1 3 = S 1 3 + S 0 1 * B 0 3 := by
    rw [B_at 1 3 (by decide), A13, A10]
    ring
  have B14 : B 1 4 = S 1 4 - S 0 1 := by
    rw [B_at 1 4 (by decide), A14, A10, B04]
    ring
  have B23 : B 2 3 = S 2 3 + S 0 2 * B 0 3 := by
    rw [B_at 2 3 (by decide), A23, A20]
    ring
  have B24 : B 2 4 = S 2 4 - S 0 2 := by
    rw [B_at 2 4 (by decide), A24, A20, B04]
    ring
  have B31 : B 3 1 = -S 1 3 + S 0 3 * B 0 1 := by
    rw [B_at 3 1 (by decide), A31, A30]
    ring
  have B32 : B 3 2 = -S 2 3 + S 0 3 * B 0 2 := by
    rw [B_at 3 2 (by decide), A32, A30]
    ring
  have B33 : B 3 3 = S 0 3 * (S 3 4 - S 0 3) / S 0 4 := by
    rw [B_at 3 3 (by decide), A33, A30, B03]
    ring
  have B34 : B 3 4 = S 3 4 - S 0 3 := by
    rw [B_at 3 4 (by decide), A34, A30, B04]
    ring
  have B41 : B 4 1 = -S 0 1 := by
    rw [B_at 4 1 (by decide), A41, A40, B01]
    field_simp [hq]
    ring
  have B42 : B 4 2 = -S 0 2 := by
    rw [B_at 4 2 (by decide), A42, A40, B02]
    field_simp [hq]
    ring
  have B43 : B 4 3 = -S 0 3 := by
    rw [B_at 4 3 (by decide), A43, A40, B03]
    field_simp [hq]
    ring
  have B44 : B 4 4 = -S 0 4 := by
    rw [B_at 4 4 (by decide), A44, A40, B04]
    ring
  have C_at (i j : Fin 5) (hi : i ≠ 3) :
      C i j = B i j - B i 3 * (B 3 j / B 3 3) := by
    dsimp [C]
    simp only [gjPivot, if_neg hi]
  have C44 : C 4 4 = 0 := by
    rw [C_at 4 4 (by decide), B44, B43, B34, B33]
    field_simp [ha, hd, hq]
    ring
  have C14 :
      C 1 4 =
        (S 0 3 * (S 1 4 - S 0 1) - S 1 3 * S 0 4 -
          S 0 1 * (S 3 4 - S 0 3)) / S 0 3 := by
    rw [C_at 1 4 (by decide), B14, B13, B34, B33, B03]
    field_simp [ha, hd, hq]
    ring
  have C41 :
      C 4 1 =
        (S 0 3 * (S 1 4 - S 0 1) - S 1 3 * S 0 4 -
          S 0 1 * (S 3 4 - S 0 3)) / (S 3 4 - S 0 3) := by
    rw [C_at 4 1 (by decide), B41, B43, B31, B33, B01]
    field_simp [ha, hd, hq]
    ring
  have C24 :
      C 2 4 =
        (S 0 3 * (S 2 4 - S 0 2) - S 2 3 * S 0 4 -
          S 0 2 * (S 3 4 - S 0 3)) / S 0 3 := by
    rw [C_at 2 4 (by decide), B24, B23, B34, B33, B03]
    field_simp [ha, hd, hq]
    ring
  have C42 :
      C 4 2 =
        (S 0 3 * (S 2 4 - S 0 2) - S 2 3 * S 0 4 -
          S 0 2 * (S 3 4 - S 0 3)) / (S 3 4 - S 0 3) := by
    rw [C_at 4 2 (by decide), B42, B43, B32, B33, B02]
    field_simp [ha, hd, hq]
    ring
  have hpair : SmaleNinth.pairedPivot5 S = C := by
    rfl
  rw [hpair]
  refine ⟨C44, ?_, ?_⟩
  · rw [C14, C41]
    field_simp [ha, hd]
  · rw [C24, C42]
    field_simp [ha, hd]
