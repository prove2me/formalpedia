-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_upper_bound__p2m_8514b45e_f592_4fc5_88fb_d0f4ef7fe022_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:48.978203+00:00
-- url     : https://prove2.me/submissions/7ec56262-028c-4350-8b87-cfc86ed1d39f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
import Theorems.Thm_WilliamsonShmoys_edge_card_mono_of_subgraph__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨K, hHK, hconn, hKplanar⟩ :=
    WilliamsonShmoys.planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a2 H hH hcard
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hmono :=
    WilliamsonShmoys.edge_card_mono_of_subgraph__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1 H K hHK
  have heuler :=
    WilliamsonShmoys.connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1 K hKplanar hconn hcard
  omega