-- Prove2me | solution 1 for SubsetShrink.L1.eq_37
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:49:20.132982+00:00
-- url     : https://prove2.me/submissions/a078144f-646c-4000-a063-ebe105e46be9

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model

set_option autoImplicit false
open SubsetShrink.L1

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (fstar ε : Fin n → ℝ) (k : ℕ) (lam : ℝ)
    (βhat β : Fin p → ℝ)
    (hbest : IsL1BestSubset X (fun i => fstar i + ε i) k lam βhat)
    (hβ : SubsetShrink.Events.l0 β ≤ k) :
    predictionError X fstar βhat + lam * SubsetShrink.Events.l1 βhat ≤
      predictionError X fstar β + 2 * SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) + lam * SubsetShrink.Events.l1 β := by
  have h := hbest.2 β hβ
  have key : ∀ a : Fin n → ℝ, ∑ i, ((fstar i + ε i) - a i) ^ 2
      = ∑ i, (fstar i - a i) ^ 2 + 2 * ∑ i, ε i * (fstar i - a i) + ∑ i, ε i ^ 2 := by
    intro a
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [key, key] at h
  have hd : ∑ i, ε i * (fstar i - X.mulVec βhat i)
      = ∑ i, ε i * (fstar i - X.mulVec β i) - SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) := by
    unfold SubsetShrink.Events.dot
    rw [Matrix.mulVec_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  unfold predictionError
  linarith
