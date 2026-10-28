-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_20261027
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:47:12.631774+00:00
-- url     : https://prove2.me/submissions/28949197-1200-4dc2-97cd-ca72deeea13f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_for_arbitrary_drawing_20261027_caef8af6
import Theorems.Thm_WilliamsonShmoys_planar_full_edge_supergraph_20261027_caef8af6

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.planar_full_edge_supergraph_20261027_caef8af6 H hV hDraw
  have hKH : K.edgeSet.ncard ≤ H.edgeSet.ncard := hMax K hsub hKdraw
  have hupper :=
    WilliamsonShmoys.planar_edge_count_bound_for_arbitrary_drawing_20261027_caef8af6
      H hV hDraw
  omega