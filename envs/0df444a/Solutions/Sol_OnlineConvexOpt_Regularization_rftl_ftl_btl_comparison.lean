-- Prove2me | solution 1 for OnlineConvexOpt.Regularization.rftl_ftl_btl_comparison
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:00:06.951896+00:00
-- url     : https://prove2.me/submissions/c5c66920-c6b9-41ce-a98b-0d6981ef4688

import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization

namespace OnlineConvexOpt.Regularization

theorem aux_btl_G {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : ℝ) (R : E → ℝ) (grad : ℕ → E) (t : ℕ) (y : E) :
    ∑ n ∈ Finset.range (t + 1 + 1), gFun η R grad n y =
      (1 / η) * R y + ∑ s ∈ Finset.range (t + 1), ⟪grad s, y⟫_ℝ := by
  rw [Finset.sum_range_succ']
  simp only [gFun]
  ring

theorem aux_btl_min {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (R : E → ℝ) (η : ℝ) (hη : 0 < η) (grad : ℕ → E) (t : ℕ) (p : E)
    (hp : IsArgMinOn (fun y => η * (∑ s ∈ Finset.range (t + 1), ⟪grad s, y⟫_ℝ) + R y) K p)
    (u : E) (hu : u ∈ K) :
    ∑ n ∈ Finset.range (t + 1 + 1), gFun η R grad n p ≤
      ∑ n ∈ Finset.range (t + 1 + 1), gFun η R grad n u := by
  rw [aux_btl_G, aux_btl_G]
  have h := hp.2 u hu
  simp only at h
  have e1 : (1 / η) * R p + ∑ s ∈ Finset.range (t + 1), ⟪grad s, p⟫_ℝ
      = (η * (∑ s ∈ Finset.range (t + 1), ⟪grad s, p⟫_ℝ) + R p) / η := by
    field_simp
    ring
  have e2 : (1 / η) * R u + ∑ s ∈ Finset.range (t + 1), ⟪grad s, u⟫_ℝ
      = (η * (∑ s ∈ Finset.range (t + 1), ⟪grad s, u⟫_ℝ) + R u) / η := by
    field_simp
    ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right h hη.le

theorem aux_btl_main {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (K : Set E) (R : E → ℝ) (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ) (x grad : ℕ → E)
    (hRun : IsRFTLRun K R η f x grad) (T : ℕ) :
    ∀ u ∈ K, ∑ n ∈ Finset.range (T + 1), gFun η R grad n (x n) ≤
      ∑ n ∈ Finset.range (T + 1), gFun η R grad n u := by
  induction T with
  | zero =>
    intro u hu
    simp only [zero_add, Finset.sum_range_one, gFun]
    have h := hRun.1.2 u hu
    have : 0 ≤ 1 / η := by positivity
    exact mul_le_mul_of_nonneg_left h this
  | succ T ih =>
    intro u hu
    have hmem : x (T + 1) ∈ K := (hRun.2.2 T).1
    have h1 := ih (x (T + 1)) hmem
    rw [Finset.sum_range_succ (fun n => gFun η R grad n (x n))]
    calc ∑ n ∈ Finset.range (T + 1), gFun η R grad n (x n) + gFun η R grad (T + 1) (x (T + 1))
        ≤ ∑ n ∈ Finset.range (T + 1), gFun η R grad n (x (T + 1))
            + gFun η R grad (T + 1) (x (T + 1)) := by linarith
      _ = ∑ n ∈ Finset.range (T + 1 + 1), gFun η R grad n (x (T + 1)) := by
            rw [Finset.sum_range_succ _ (T + 1)]
      _ ≤ ∑ n ∈ Finset.range (T + 1 + 1), gFun η R grad n u :=
            aux_btl_min K R η hη grad T (x (T + 1)) (hRun.2.2 T) u hu

end OnlineConvexOpt.Regularization

open OnlineConvexOpt.Regularization

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (R : E → ℝ) (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ) (x grad : ℕ → E)
    (hRun : IsRFTLRun K R η f x grad) (T : ℕ) (u : E) (hu : u ∈ K) :
    ∑ n ∈ Finset.range (T + 1), gFun η R grad n u ≥
      ∑ n ∈ Finset.range (T + 1), gFun η R grad n (x n) :=
  aux_btl_main K R η hη f x grad hRun T u hu
