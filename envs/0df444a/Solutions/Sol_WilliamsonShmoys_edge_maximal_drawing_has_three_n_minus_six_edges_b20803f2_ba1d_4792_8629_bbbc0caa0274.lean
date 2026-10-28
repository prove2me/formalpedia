-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_drawing_has_three_n_minus_six_edges_b20803f2_ba1d_4792_8629_bbbc0caa0274
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:01:40.104128+00:00
-- url     : https://prove2.me/submissions/6d9a695c-066c-4c2e-b9f6-d7a88d441169
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_retry2
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_retry2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hSub, hLDraw, hLower⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_retry2 K hDraw hCard
  have hEq : L = K := hMax L hSub hLDraw
  subst L
  have hUpper :=
    WilliamsonShmoys.planar_simple_graph_edge_bound_retry2 K hDraw hCard
  omega