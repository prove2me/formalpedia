-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_b5de7163_4173_4d75_853e_5e2f32ae30ae_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:51:19.742849+00:00
-- url     : https://prove2.me/submissions/b08ec82d-e26d-43a4-9ba0-3f77ac7d3bc6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_5253a5b4_e9a3_4062_83c0_61b2b3da7c3e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_5253a5b4_e9a3_4062_83c0_61b2b3da7c3e_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_5253a5b4_e9a3_4062_83c0_61b2b3da7c3e_a1
    H hplanar hmax hcard
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_5253a5b4_e9a3_4062_83c0_61b2b3da7c3e_a1
    H hplanar hmax hcard
  omega