-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_augmentation__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:34:12.285762+00:00
-- url     : https://prove2.me/submissions/0c7b2069-5f86-4f45-a69b-89f14d512809
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      G <= H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel _;
       3 * Fintype.card V - 6 <= H.edgeFinset.card) := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1
      G hG
  refine ⟨H, hGH, hH, ?_⟩
  letI : DecidableRel H.Adj := Classical.decRel _
  exact WilliamsonShmoys.maximal_planar_edge_bound__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1
    H hH hcard hmax