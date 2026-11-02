-- Prove2me | solution 1 for WilliamsonShmoys.extract_added_edge_as_bridge__p2m_f0a53f14_3d07_482d_8483_9c70fdc17ecd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:57:16.398838+00:00
-- url     : https://prove2.me/submissions/cc0398c6-30a5-488b-a1d1-d71098002213

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_extract_added_edge_as_bridge_geometric_core__p2m_13580833_cd4c_44e5_a8be_55495eb3e767_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (u v : V) (hnot : ¬ H.Reachable u v)
    (hAug : HasPlanarDrawingOn (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)})) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
      (bridge : ℝ → ℝ × ℝ),
      Function.Injective p ∧
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
      ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn bridge (Set.Icc (0 : ℝ) 1) ∧
      bridge 0 = p u ∧ bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  rcases hAug with ⟨p, arc, hp, hAugEdge, hAugCross⟩
  have hCore := WilliamsonShmoys.extract_added_edge_as_bridge_geometric_core__p2m_13580833_cd4c_44e5_a8be_55495eb3e767_a2
    H u v p arc hp hAugEdge hAugCross hnot
  rcases hCore with ⟨hOriginalEdge, hOriginalCross, bridge, hBridgeCont,
    hBridgeInj, hBridge0, hBridge1, hBridgeAvoid, hBridgeCross⟩
  exact ⟨p, arc, bridge, hp, hOriginalEdge, hOriginalCross,
    hBridgeCont, hBridgeInj, hBridge0, hBridge1, hBridgeAvoid, hBridgeCross⟩