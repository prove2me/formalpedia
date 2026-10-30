-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_77f664a0
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:57:40.575818+00:00
-- url     : https://prove2.me/submissions/6ec2f4ff-f790-4a76-b9d0-5c90aabc676d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_77f664a0
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_77f664a0

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHDraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_77f664a0 G hCard hDraw
  have hEdges := WilliamsonShmoys.maximal_planar_drawing_edge_count_77f664a0 H hCard hHDraw hMax
  have hle : G.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hGH
  omega