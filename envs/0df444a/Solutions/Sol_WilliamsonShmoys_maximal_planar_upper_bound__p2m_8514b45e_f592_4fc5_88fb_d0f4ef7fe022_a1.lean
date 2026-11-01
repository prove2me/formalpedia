-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_upper_bound__p2m_8514b45e_f592_4fc5_88fb_d0f4ef7fe022_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:16:17.955185+00:00
-- url     : https://prove2.me/submissions/875ba577-b96b-4da0-882d-03594eb0a227
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
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
    WilliamsonShmoys.planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1 H hH
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hmono := WilliamsonShmoys.edge_card_mono_of_subgraph__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1 H K hHK
  have heuler := WilliamsonShmoys.connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1 K hKplanar hconn hcard
  omega