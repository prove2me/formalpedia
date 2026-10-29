-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_dense_completion__p2m_a1bc3295_288e_4dac_b293_e5c76a636381_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:34:37.24699+00:00
-- url     : https://prove2.me/submissions/2eb532fc-10d9-4835-bd0d-0cf8aac9857e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_is_dense__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      L ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  obtain ⟨N, hLN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_completion__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1 L hL
  exact ⟨N, hLN, hN,
    WilliamsonShmoys.maximal_planar_graph_is_dense__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1 N hN hV hmax⟩