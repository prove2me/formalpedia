-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count_edge_bound_20261028
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:46:49.406562+00:00
-- url     : https://prove2.me/submissions/d67369cc-ed21-4301-a46f-5338e86dfa18

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula_from_crossing_free_drawing
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_from_crossing_free_drawing

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ F : ℕ, Fintype.card V + F = G.edgeSet.ncard + 2 ∧
      3 * F ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨F, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_formula_from_crossing_free_drawing
      G hV hConnected hDraw
  have hEdge :=
    WilliamsonShmoys.planar_simple_graph_edge_bound_from_crossing_free_drawing
      G hV hConnected hDraw
  refine ⟨F, hEuler, ?_⟩
  omega