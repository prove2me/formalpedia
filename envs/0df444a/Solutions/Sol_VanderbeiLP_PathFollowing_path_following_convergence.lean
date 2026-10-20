-- Prove2me | solution 1 for VanderbeiLP.PathFollowing.path_following_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:18:53.381438+00:00
-- url     : https://prove2.me/submissions/1360b4e3-a4d6-427f-81b1-014962c12721

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_primal_decay
import Theorems.Thm_p2m_dual_decay
import Theorems.Thm_p2m_normInf_nonneg
import Theorems.Thm_p2m_norm1_nonneg
import Theorems.Thm_p2m_stepLength_le_one
import Theorems.Thm_p2m_complementarity_step
import Theorems.Thm_p2m_complementarity_recurrence
import Theorems.Thm_p2m_path_geometric_recurrence_upto

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
    ∀ k ≤ K,
      norm1 (primalInfeas A b (s k)) ≤ (1 - t) ^ k * norm1 (primalInfeas A b (s 0)) ∧
      norm1 (dualInfeas A c (s k)) ≤ (1 - t) ^ k * norm1 (dualInfeas A c (s 0)) ∧
      complementarity (s k) ≤
        (1 - t * (1 - δ)) ^ k
          * (complementarity (s 0)
              + M * (norm1 (primalInfeas A b (s 0)) + norm1 (dualInfeas A c (s 0)))
                / (δ * t)) := by
  have ht1 : t ≤ 1 := le_trans (hθ 0 (Nat.zero_le K))
    (p2m_stepLength_le_one r (s 0) (d 0))
  have hM : 0 ≤ M := le_trans (p2m_normInf_nonneg (s 0).x) (hx 0 (Nat.zero_le K))
  let R := norm1 (primalInfeas A b (s 0)) + norm1 (dualInfeas A c (s 0))
  have hR : 0 ≤ R := add_nonneg (p2m_norm1_nonneg _) (p2m_norm1_nonneg _)
  have hone : ∀ k ≤ K,
      complementarity (s (k + 1)) ≤
        (1 - (1 - δ) * stepLength r (s k) (d k)) * complementarity (s k)
          + M * norm1 (primalInfeas A b (s k)) + M * norm1 (dualInfeas A c (s k)) := by
    intro k hk
    exact p2m_complementarity_step A b c δ r hδ0 hδ1 hr0 hr1
      (s k) (d k) (s (k + 1)) (hstep k hk) M (hx k hk) (hy k hk)
  have hrec := p2m_complementarity_recurrence A b c δ r t M hδ0 hδ1 hr0 hr1
    s d K hstep hθ hx hy hone
  have hcomp := p2m_path_geometric_recurrence_upto K hδ0 hδ1 ht ht1 hM hR
    (fun k => complementarity (s k)) hrec
  intro k hk
  exact ⟨p2m_primal_decay A b c δ r t hδ0 hδ1 hr0 hr1 s d K hstep hθ k hk,
    p2m_dual_decay A b c δ r t hδ0 hδ1 hr0 hr1 s d K hstep hθ k hk,
    hcomp k hk⟩
