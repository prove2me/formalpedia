-- Prove2me | solution 2 for WrightPDIPM.PathFollowing.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:09:54.990886+00:00
-- url     : https://prove2.me/submissions/1129fe41-bb14-4d17-9009-86888e613aeb

import Mathlib
import Definitions.Def_WrightPDIPM_PathFollowing_Setup
set_option autoImplicit false
open Matrix

theorem solution {n : ℕ} (u v : Fin n → ℝ) (huv : 0 ≤ u ⬝ᵥ v) :
    WrightPDIPM.PathFollowing.norm2 (fun i => u i * v i) ≤
      (2 : ℝ) ^ (-((3 : ℝ) / 2)) * WrightPDIPM.PathFollowing.norm2 (u + v) ^ 2 := by
  unfold WrightPDIPM.PathFollowing.norm2
  set s : ℝ := ∑ i, (u + v) i ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [Real.sq_sqrt hs0]
  -- key polynomial inequality
  have sq_le : ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → ∑ i, a i ^ 2 ≤ (∑ i, a i) ^ 2 := by
    intro a ha
    rw [sq, Finset.sum_mul_sum]
    calc ∑ i, a i ^ 2 = ∑ i, a i * a i := by simp [sq]
      _ ≤ ∑ i, ∑ j, a i * a j := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.single_le_sum (f := fun j => a i * a j)
            (fun j _ => mul_nonneg (ha i) (ha j)) (Finset.mem_univ i)
  have hdot : u ⬝ᵥ v = ∑ i, u i * v i := rfl
  set P : Fin n → ℝ := fun i => (u i + v i) ^ 2 with hP
  set M : Fin n → ℝ := fun i => (u i - v i) ^ 2 with hM
  have hPs : ∑ i, P i = s := by simp [hP, hs]
  have hMs : ∑ i, M i = s - 4 * (u ⬝ᵥ v) := by
    rw [hdot, ← hPs, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; simp only [hP, hM]; ring
  have hP0 : ∀ i, 0 ≤ P i := fun i => sq_nonneg _
  have hM0 : ∀ i, 0 ≤ M i := fun i => sq_nonneg _
  have h1 : ∑ i, P i ^ 2 ≤ s ^ 2 := by rw [← hPs]; exact sq_le P hP0
  have hMnn : 0 ≤ ∑ i, M i := Finset.sum_nonneg (fun i _ => hM0 i)
  have h2 : ∑ i, M i ^ 2 ≤ s ^ 2 := by
    refine (sq_le M hM0).trans ?_
    rw [hMs] at hMnn ⊢
    nlinarith
  have h3 : ∑ i, (u i * v i) ^ 2 ≤ s ^ 2 / 8 := by
    have : ∀ i, (u i * v i) ^ 2 ≤ (P i ^ 2 + M i ^ 2) / 16 := by
      intro i
      have e : u i * v i = (P i - M i) / 4 := by simp only [hP, hM]; ring
      rw [e]
      nlinarith [mul_nonneg (hP0 i) (hM0 i)]
    calc ∑ i, (u i * v i) ^ 2 ≤ ∑ i, (P i ^ 2 + M i ^ 2) / 16 := Finset.sum_le_sum (fun i _ => this i)
      _ = (∑ i, P i ^ 2 + ∑ i, M i ^ 2) / 16 := by rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ s ^ 2 / 8 := by linarith
  -- conclude
  have hc : (2 : ℝ) ^ (-((3 : ℝ) / 2)) = Real.sqrt (1 / 8) := by
    rw [show (1 / 8 : ℝ) = (2 : ℝ) ^ (-(3 : ℝ)) by
      rw [Real.rpow_neg (by norm_num)]
      norm_num [Real.rpow_natCast]]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [hc]
  calc Real.sqrt (∑ i, (u i * v i) ^ 2) ≤ Real.sqrt (1 / 8 * s ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
    _ = Real.sqrt (1 / 8) * s := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hs0]
