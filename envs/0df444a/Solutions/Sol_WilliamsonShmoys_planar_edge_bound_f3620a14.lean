-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_f3620a14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:39:45.027323+00:00
-- url     : https://prove2.me/submissions/c901c154-071f-4a43-be9b-859440255407
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_eb9e91c8
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_eb9e91c8
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_eb9e91c8

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hTH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension_eb9e91c8 T hT hCard
  have hCount := WilliamsonShmoys.maximal_planar_graph_edge_count_eb9e91c8 H hH hMax hCard
  have hMono := WilliamsonShmoys.edgeSet_ncard_mono_eb9e91c8 T H hTH
  omega
