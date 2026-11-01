-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_5253a5b4_e9a3_4062_83c0_61b2b3da7c3e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:05:49.780224+00:00
-- url     : https://prove2.me/submissions/11a0010e-1702-4780-90e8-421a4857a08b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_facial_count__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1
import Theorems.Thm_WilliamsonShmoys_planar_facial_count_arithmetic__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨f, heuler, htri⟩ :=
    WilliamsonShmoys.planar_facial_count__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1
      H hplanar hmax hcard
  exact WilliamsonShmoys.planar_facial_count_arithmetic__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1
    (Fintype.card V) H.edgeSet.ncard f heuler htri