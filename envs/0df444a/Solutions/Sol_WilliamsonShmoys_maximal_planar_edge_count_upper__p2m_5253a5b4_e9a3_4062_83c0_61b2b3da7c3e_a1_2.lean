-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_5253a5b4_e9a3_4062_83c0_61b2b3da7c3e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:22:50.859945+00:00
-- url     : https://prove2.me/submissions/0443c897-067b-43f7-8000-8ca87028a94f

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1 H hplanar hcard
