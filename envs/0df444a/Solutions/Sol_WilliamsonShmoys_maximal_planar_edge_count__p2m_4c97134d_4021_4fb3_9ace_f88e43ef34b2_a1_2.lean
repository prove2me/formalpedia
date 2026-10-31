-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:32:04.995007+00:00
-- url     : https://prove2.me/submissions/133da42c-c2c6-425e-8e0e-17b6ac40d7b7

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) : H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1 H hCard hH hmax
