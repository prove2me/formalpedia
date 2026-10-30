-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_add_bridge__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:58:11.282345+00:00
-- url     : https://prove2.me/submissions/d795f601-9e98-44c0-a68d-8c0cd42a2ca0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_bridge_curve__p2m_0429bc33_fbf6_41dd_a067_66ab7d02dd4c_a3
import Theorems.Thm_WilliamsonShmoys_planar_add_bridge_of_bridge_curve__p2m_0429bc33_fbf6_41dd_a067_66ab7d02dd4c_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (x y : V)
    (hxy : ¬ G.Reachable x y) :
    ∃ N : SimpleGraph V,
      G ≤ N ∧
      (∀ u v, N.Adj u v ↔
        G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) ∧
      HasPlanarDrawingOn N := by
  obtain ⟨p, arc, γ, hDrawing, hBridge⟩ :=
    WilliamsonShmoys.disconnected_planar_drawing_has_bridge_curve__p2m_0429bc33_fbf6_41dd_a067_66ab7d02dd4c_a3
      G hG x y hxy
  exact WilliamsonShmoys.planar_add_bridge_of_bridge_curve__p2m_0429bc33_fbf6_41dd_a067_66ab7d02dd4c_a3
    G x y hxy p arc γ hDrawing hBridge
