-- Prove2me | solution 1 for WilliamsonShmoys.finite_simple_graph_set_has_maximal_member__p2m_e1cd0124_e641_4ece_baff_4e3ebf9bbef8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:59:13.687164+00:00
-- url     : https://prove2.me/submissions/58728611-bf75-424c-85b1-c860f8a184c1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (S : Set (SimpleGraph V)) (hS : S.Nonempty) :
    ∃ G : SimpleGraph V, G ∈ S ∧
      ∀ H : SimpleGraph V, H ∈ S → G ≤ H → H ≤ G := by
  classical
  obtain ⟨G, hG, hmax⟩ := (Set.toFinite S).exists_maximal hS
  exact ⟨G, hG, fun H hH hGH => hmax hH hGH⟩