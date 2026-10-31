-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:57:01.810146+00:00
-- url     : https://prove2.me/submissions/11765db6-2afc-4aa8-88bc-7abd3f04c082
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_6e30398e_7f8d_44b8_bb51_ffb2d64a0829_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_6e30398e_7f8d_44b8_bb51_ffb2d64a0829_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨M, hGM, hM, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_6e30398e_7f8d_44b8_bb51_ffb2d64a0829_a1
      G hG
  have hle : G.edgeSet.ncard ≤ M.edgeSet.ncard := Set.ncard_mono hGM
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_6e30398e_7f8d_44b8_bb51_ffb2d64a0829_a1
      M hCard hM hMax
  omega