-- Prove2me | solution 1 for VanderbeiLP.PathFollowing.complementarity_recursion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:08:46.261158+00:00
-- url     : https://prove2.me/submissions/f016aaf1-c39e-4df6-ac9a-1a9c35467b88

import Mathlib.LinearAlgebra.Matrix.Defs
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_complementarity_recurrence
import Theorems.Thm_p2m_complementarity_step
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (s d : ℕ → PDPoint m n) (t M : ℝ) (K : ℕ) (ht : 0 < t)
    (hstep : ∀ k ≤ K, IsPathFollowingStep A b c δ r (s k) (d k) (s (k + 1)))
    (hθ : ∀ k ≤ K, t ≤ stepLength r (s k) (d k))
    (hx : ∀ k ≤ K, normInf (s k).x ≤ M) (hy : ∀ k ≤ K, normInf (s k).y ≤ M) :
    ∀ k, k + 1 ≤ K →
      complementarity (s (k + 1)) ≤
        (1 - t * (1 - δ)) * complementarity (s k)
          + M * (1 - t) ^ k
            * (norm1 (primalInfeas A b (s 0)) + norm1 (dualInfeas A c (s 0))) := by
  have hone : ∀ k ≤ K,
      complementarity (s (k + 1)) ≤
        (1 - (1 - δ) * stepLength r (s k) (d k)) * complementarity (s k)
          + M * norm1 (primalInfeas A b (s k)) + M * norm1 (dualInfeas A c (s k)) := by
    intro k hk
    exact p2m_complementarity_step A b c δ r hδ0 hδ1 hr0 hr1
      (s k) (d k) (s (k + 1)) (hstep k hk) M (hx k hk) (hy k hk)
  exact p2m_complementarity_recurrence A b c δ r t M hδ0 hδ1 hr0 hr1
    s d K hstep hθ hx hy hone
