-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_exists__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:40:33.018854+00:00
-- url     : https://prove2.me/submissions/da6d03f8-d3b1-4c84-a197-f26fca6b60c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_by_edge_card__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1
import Theorems.Thm_WilliamsonShmoys_edge_card_lt_of_le_not_le__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ H : SimpleGraph V, L ≤ H →
          WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L := by
  classical
  obtain ⟨L, hLdec, hGL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_by_edge_card__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1
      G hG
  letI : DecidableRel L.Adj := hLdec
  refine ⟨L, hGL, hL, ?_⟩
  intro H hLH hH
  have hGH : G ≤ H := le_trans hGL hLH
  have hcard := hmax H hGH hH
  by_contra hnot
  have hlt :=
    WilliamsonShmoys.edge_card_lt_of_le_not_le__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1
      L H hLH hnot
  omega