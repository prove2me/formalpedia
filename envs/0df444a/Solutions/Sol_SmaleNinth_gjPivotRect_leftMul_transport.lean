-- Prove2me | solution 1 for SmaleNinth.gjPivotRect_leftMul_transport
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:03:02.528036+00:00
-- url     : https://prove2.me/submissions/509b0a03-b090-407e-b78a-980b568e6a33

import Mathlib
import Definitions.Def_SmaleNinth_GaussJordanPlus

open Matrix in
theorem solution {r c : ℕ}
    (S : Matrix (Fin r) (Fin c) ℝ) (i : Fin r) (j : Fin c)
    (hp : S i j ≠ 0) (y : Fin r → ℝ) :
    (fun a : Fin r =>
      if a = i then
        S i j * y i + ∑ b ∈ (Finset.univ : Finset (Fin r)).erase i, y b * S b j
      else y a) ᵥ* SmaleNinth.gjPivotRect S i j = y ᵥ* S := by
  funext b
  simp only [vecMul, dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h1 : ∀ a ∈ (Finset.univ : Finset (Fin r)).erase i,
      (if a = i then S i j * y i + ∑ b ∈ (Finset.univ : Finset (Fin r)).erase i, y b * S b j
        else y a) * SmaleNinth.gjPivotRect S i j a b
        = y a * S a b - (y a * S a j) * (S i b / S i j) := by
    intro a ha
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    simp only [SmaleNinth.gjPivotRect, if_neg hai]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [SmaleNinth.gjPivotRect, eq_self_iff_true, if_true]
  have hk : S i j * y i * (S i b / S i j) = y i * S i b := by
    field_simp
  rw [add_mul, hk]
  ring
