-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_73f2721b_9638_40de_84f2_73b0dfd4838a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:58:48.813168+00:00
-- url     : https://prove2.me/submissions/08fb6508-9148-4221-9475-43b2a12e2b0e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    Exists fun T : SimpleGraph V =>
      And (G.edgeSet ⊆ T.edgeSet)
        (And (HasPlanarDrawingOn T)
          (T.edgeSet.ncard + 6 = 3 * Fintype.card V)) := by
  obtain ⟨T, hGT, hT, hMax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1
      G hG
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1
      T hT hMax hV
  exact ⟨T, hGT, hT, hCount⟩