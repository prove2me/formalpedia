-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_ge
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:10:53.395212+00:00
-- url     : https://prove2.me/submissions/b6c4bbe2-6e04-4e4e-9e90-4f40474e986c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_20261027
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_euler_20261027

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : forall Q : SimpleGraph V,
      (forall {u v}, P.Adj u v -> Q.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn Q -> Q = P)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= P.edgeSet.ncard := by
  obtain ⟨Q, hPQ, hQdraw, hQmax⟩ :=
    WilliamsonShmoys.finite_maximal_drawable_supergraph_20261027 P hdraw
  have hQP : Q = P := hmax Q hPQ hQdraw
  have hQcard := WilliamsonShmoys.maximal_drawable_edge_count_euler_20261027
    Q hQdraw hQmax hV
  rw [hQP] at hQcard
  omega