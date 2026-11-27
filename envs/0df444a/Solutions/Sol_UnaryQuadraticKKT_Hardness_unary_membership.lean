-- Prove2me | solution 1 for UnaryQuadraticKKT.Hardness.unary_membership
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:51:44.09472+00:00
-- url     : https://prove2.me/submissions/3115f1e9-4eb1-4cac-aa01-023eef26565c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Output
import Theorems.Thm_UnaryQuadraticKKT_Hardness_unary_short_kkt
import Theorems.Thm_UnaryQuadraticKKT_Hardness_unary_kkt_checkable
import Theorems.Thm_UnaryQuadraticKKT_Hardness_unary_cls_reduction_eventually

open NetworkEquilibriumCLS.LinearNash UnaryQuadraticKKT.Hardness

theorem bounded_total_mono' (S : SearchProblem) (k k' : ℕ) (hk : k ≤ k')
    (h : TotalSearch (bounded S k)) : TotalSearch (bounded S k') := by
  intro x hx
  obtain ⟨y, hy, hlen⟩ := h x hx
  refine ⟨y, hy, le_trans hlen ?_⟩
  have : (x.length + 1) ^ k ≤ (x.length + 1) ^ k' := Nat.pow_le_pow_right (by omega) hk
  omega

theorem solution : ∃ b : ℕ, InCLS (bounded unarySearch b) := by
  obtain ⟨k0, hk0⟩ := unary_short_kkt
  obtain ⟨K, hK⟩ := unary_cls_reduction_eventually
  refine ⟨max k0 K, ⟨⟨bounded_total_mono' _ _ _ (le_max_left _ _) hk0, ⟨max k0 K, ?_⟩,
    unary_kkt_checkable _⟩, hK _ (le_max_right _ _)⟩⟩
  intro x y _ hy
  exact hy.2
