-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulating_supergraph__p2m_d1b6a74a_dd8a_4218_af86_64a379555708_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:24:04.764422+00:00
-- url     : https://prove2.me/submissions/ac222122-5d2c-457a-8c6b-008270041268
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V => H <= K /\ HasPlanarDrawingOn K /\
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1 H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1 K hK hV hmax⟩