-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:54:54.212279+00:00
-- url     : https://prove2.me/submissions/5c1566f3-af49-44d8-aaea-b577402ef2bd

import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_from_drawing_v2
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨M, hsub, hMdraw, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension N hNdraw
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound_from_drawing_v2
      M hV hMdraw hmax
  have hcard : N.edgeSet.ncard ≤ M.edgeSet.ncard := Set.ncard_mono hsub
  omega