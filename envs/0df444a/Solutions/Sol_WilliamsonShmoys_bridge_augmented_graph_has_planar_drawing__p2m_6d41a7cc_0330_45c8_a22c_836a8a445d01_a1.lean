-- Prove2me | solution 1 for WilliamsonShmoys.bridge_augmented_graph_has_planar_drawing__p2m_6d41a7cc_0330_45c8_a22c_836a8a445d01_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:11:07.755045+00:00
-- url     : https://prove2.me/submissions/0237ba65-9cc5-4fd7-881f-cf3f3f652f57

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_bridge_augmented_graph_adj_iff__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4
import Theorems.Thm_WilliamsonShmoys_has_planar_drawingOn_single_edge_extension__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdges : ∀ a b, a < b → H.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hCross : ∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
      (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc a b t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (c : ℝ → ℝ × ℝ)
    (huv : u < v)
    (hccont : ContinuousOn c (Set.Icc 0 1))
    (hcinj : Set.InjOn c (Set.Icc 0 1))
    (hc0 : c 0 = p u)
    (hc1 : c 1 = p v)
    (hcvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w)
    (hccross : ∀ x y, x < y → H.Adj x y → (u, v) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        c t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    HasPlanarDrawingOn
      (H ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)) := by
  apply WilliamsonShmoys.has_planar_drawingOn_single_edge_extension__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4
    H (H ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)) p arc hp hEdges hCross u v c huv
    hccont hcinj hc0 hc1 hcvertices hccross
  intro a b hab
  exact WilliamsonShmoys.bridge_augmented_graph_adj_iff__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4
    H u v huv a b hab