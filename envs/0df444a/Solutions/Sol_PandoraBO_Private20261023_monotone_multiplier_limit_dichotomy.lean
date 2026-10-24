-- Prove2me | solution 1 for PandoraBO.Private20261023.monotone_multiplier_limit_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:29:44.016268+00:00
-- url     : https://prove2.me/submissions/0ca62307-2a2d-474c-8925-222afbbbcb88

import Definitions.Def_PandoraBO_Model
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
open Filter Topology

theorem solution (multipliers : ℕ → ℝ) (limit : ℝ)
    (hmono : Monotone multipliers ∨ Antitone multipliers)
    (hlim : Tendsto multipliers atTop (𝓝 limit)) :
    (Monotone multipliers ∧ ∀ k, multipliers k < limit) ∨
    (Antitone multipliers ∧ ∀ k, limit < multipliers k) ∨
    ∃ K : ℕ, ∀ k, K ≤ k → multipliers k = limit := by
  classical
  rcases hmono with hinc | hdec
  · by_cases hall : ∀ k, multipliers k < limit
    · exact Or.inl ⟨hinc, hall⟩
    · obtain ⟨K, hK⟩ := not_forall.mp hall
      have hK : limit ≤ multipliers K := le_of_not_gt hK
      right
      right
      refine ⟨K, ?_⟩
      intro k hk
      exact le_antisymm (hinc.ge_of_tendsto hlim k) (hK.trans (hinc hk))
  · by_cases hall : ∀ k, limit < multipliers k
    · exact Or.inr (Or.inl ⟨hdec, hall⟩)
    · obtain ⟨K, hK⟩ := not_forall.mp hall
      have hK : multipliers K ≤ limit := le_of_not_gt hK
      right
      right
      refine ⟨K, ?_⟩
      intro k hk
      exact le_antisymm ((hdec hk).trans hK) (hdec.le_of_tendsto hlim k)
