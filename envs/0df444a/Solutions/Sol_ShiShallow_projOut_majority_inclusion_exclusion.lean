-- Prove2me | solution 1 for ShiShallow.projOut_majority_inclusion_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T18:54:31.124222+00:00
-- url     : https://prove2.me/submissions/96acb7af-192a-4f31-b713-1c6217c95972

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

private lemma shiMajp_mul_diag {n : ℕ} (a b : Fin n) (y : Bits n) :
    (projOut a * projOut b) y y
      = (if y a = true then (1:ℂ) else 0) * (if y b = true then (1:ℂ) else 0) := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
  · simp [projOut]
  · intro w _ hw
    simp [projOut, Ne.symm hw]

private lemma shiMajp_mul_off {n : ℕ} (a b : Fin n) (y z : Bits n) (h : y ≠ z) :
    (projOut a * projOut b) y z = 0 := by
  classical
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero ?_
  intro w _
  by_cases hw : y = w
  · subst hw
    simp [projOut, h]
  · simp [projOut, hw]

private lemma shiMajp_mul3_diag {n : ℕ} (a b c : Fin n) (y : Bits n) :
    (projOut a * projOut b * projOut c) y y
      = (if y a = true then (1:ℂ) else 0) * (if y b = true then (1:ℂ) else 0)
          * (if y c = true then (1:ℂ) else 0) := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
  · rw [shiMajp_mul_diag]
    simp [projOut]
  · intro w _ hw
    rw [shiMajp_mul_off a b y w (Ne.symm hw)]
    simp

private lemma shiMajp_mul3_off {n : ℕ} (a b c : Fin n) (y z : Bits n) (h : y ≠ z) :
    (projOut a * projOut b * projOut c) y z = 0 := by
  classical
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero ?_
  intro w _
  by_cases hw : y = w
  · subst hw
    simp [projOut, h]
  · rw [shiMajp_mul_off a b y w hw]
    simp

theorem solution {n : ℕ} (w1 w2 w3 : Fin n) :
    (Matrix.of fun y z => if y = z ∧ 2 ≤ (if y w1 = true then (1:ℕ) else 0)
            + (if y w2 = true then (1:ℕ) else 0) + (if y w3 = true then (1:ℕ) else 0)
          then (1:ℂ) else 0)
      = projOut w1 * projOut w2 + projOut w2 * projOut w3 + projOut w3 * projOut w1
          - 2 * (projOut w1 * projOut w2 * projOut w3) := by
  classical
  rw [two_mul]
  ext y z
  by_cases h : y = z
  · subst h
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply,
      shiMajp_mul_diag, shiMajp_mul3_diag, eq_self_iff_true, true_and, and_true]
    by_cases h1 : y w1 = true <;> by_cases h2 : y w2 = true <;> by_cases h3 : y w3 = true <;>
      simp [h1, h2, h3] <;> norm_num
  · have e1 := shiMajp_mul_off w1 w2 y z h
    have e2 := shiMajp_mul_off w2 w3 y z h
    have e3 := shiMajp_mul_off w3 w1 y z h
    have e4 := shiMajp_mul3_off w1 w2 w3 y z h
    simp [Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, h, e1, e2, e3, e4]
