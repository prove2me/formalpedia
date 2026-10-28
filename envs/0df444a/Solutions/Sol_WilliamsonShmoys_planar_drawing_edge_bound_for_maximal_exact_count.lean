-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_for_maximal_exact_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:10:07.440964+00:00
-- url     : https://prove2.me/submissions/0d1e124b-e07e-4f1f-8516-0246696446ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_spanning_augmentation
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_euler

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    J.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hJK, hKconn, hKdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_spanning_augmentation J hV hJ
  have hK := WilliamsonShmoys.connected_planar_drawing_edge_bound_euler K hKconn hV hKdraw
  have hEdges : J.edgeSet ⊆ K.edgeSet :=
    (SimpleGraph.edgeSetEmbedding V).monotone hJK
  have hCard : J.edgeSet.ncard <= K.edgeSet.ncard := Set.ncard_mono hEdges
  omega