-- Prove2me | solution 1 for WilliamsonShmoys_planar_edge_count_upper_bound__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:08:02.332204+00:00
-- url     : https://prove2.me/submissions/f547f821-344f-486d-ad9d-e1668afb6c82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_maximal__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : LE.le 3 (Fintype.card V)) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨M, hGM, hMplanar, hMmax⟩ :=
    WilliamsonShmoys.planar_drawable_supergraph_maximal__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
      G hGplanar
  have hMcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
      M hMplanar hV hMmax
  have hsub : G.edgeSet ⊆ M.edgeSet := SimpleGraph.edgeSet_mono hGM
  have hcard : G.edgeSet.ncard ≤ M.edgeSet.ncard := Set.ncard_mono hsub
  omega