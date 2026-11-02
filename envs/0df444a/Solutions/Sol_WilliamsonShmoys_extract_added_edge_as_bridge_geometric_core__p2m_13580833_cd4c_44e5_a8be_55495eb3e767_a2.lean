-- Prove2me | solution 1 for WilliamsonShmoys.extract_added_edge_as_bridge_geometric_core__p2m_13580833_cd4c_44e5_a8be_55495eb3e767_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:06:05.316096+00:00
-- url     : https://prove2.me/submissions/12100b7d-3772-47cb-8225-9bce1a372b36

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_augmented_drawing_restricts_to_original__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2
import Theorems.Thm_WilliamsonShmoys_added_edge_arc_is_oriented_bridge__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2
import Theorems.Thm_WilliamsonShmoys_added_edge_bridge_meets_original_arcs_only_at_endpoints__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hAugEdge : ∀ a b, a < b →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hAugCross : ∀ a b x y, a < b → x < y →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj x y →
      (a, b) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc a b t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hnot : ¬ H.Reachable u v) :
    (∀ a b, a < b → H.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
    (∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
      (a, b) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc a b t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
    ∃ bridge : ℝ → ℝ × ℝ,
      ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn bridge (Set.Icc 0 1) ∧
      bridge 0 = p u ∧ bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  have hOriginal :=
    WilliamsonShmoys.augmented_drawing_restricts_to_original__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2
      H u v p arc hp hAugEdge hAugCross
  let bridge : ℝ → ℝ × ℝ := if u < v then arc u v else fun t => arc v u (1 - t)
  have hBridge :=
    WilliamsonShmoys.added_edge_arc_is_oriented_bridge__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2
      H u v p arc hp hAugEdge hnot
  have hCross :=
    WilliamsonShmoys.added_edge_bridge_meets_original_arcs_only_at_endpoints__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2
      H u v arc hAugCross hnot bridge rfl
  rcases hOriginal with ⟨hDraw, hOrigCross⟩
  rcases hBridge with ⟨hcont, hinj, hzero, hone, hvertex⟩
  exact ⟨hDraw, hOrigCross, ⟨bridge, hcont, hinj, hzero, hone, hvertex, hCross⟩⟩