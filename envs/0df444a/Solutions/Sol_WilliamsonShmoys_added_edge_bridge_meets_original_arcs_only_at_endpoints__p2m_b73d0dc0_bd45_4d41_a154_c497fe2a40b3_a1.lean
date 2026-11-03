-- Prove2me | solution 1 for WilliamsonShmoys.added_edge_bridge_meets_original_arcs_only_at_endpoints__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:31:18.673345+00:00
-- url     : https://prove2.me/submissions/3a3701e7-aa98-4925-b4fc-982687fe41e7

import Theorems.Thm_WilliamsonShmoys_added_edge_bridge_meets_original_arcs_only_at_endpoints__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hAugCross : ∀ a b x y, a < b → x < y →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj x y →
      (a, b) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc a b t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hnot : ¬ H.Reachable u v)
    (bridge : ℝ → ℝ × ℝ)
    (hbridge : bridge = if u < v then arc u v else fun t => arc v u (1 - t)) :
    ∀ a b, a < b → H.Adj a b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        bridge t = arc a b s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) :=
  WilliamsonShmoys.added_edge_bridge_meets_original_arcs_only_at_endpoints__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2 H u v arc hAugCross hnot bridge hbridge