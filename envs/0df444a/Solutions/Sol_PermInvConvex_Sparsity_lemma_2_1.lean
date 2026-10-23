-- Prove2me | solution 1 for PermInvConvex.Sparsity.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T05:50:29.81126+00:00
-- url     : https://prove2.me/submissions/1bcb4cf7-ab44-4f2a-bece-6973617e1dbb

import Mathlib
open Matrix
set_option autoImplicit false

theorem solution {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (S : Set (Fin n → ℝ))
    (hS : ∀ x ∈ S, T *ᵥ x ∈ S) :
    ∀ x ∈ convexHull ℝ S, T *ᵥ x ∈ convexHull ℝ S := by
  exact convexHull_min (fun x hx => subset_convexHull ℝ S (hS x hx))
    ((convex_convexHull ℝ S).linear_preimage T.mulVecLin)
