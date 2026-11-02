-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound__p2m_a7b1543f_eb9f_42ef_b47d_96ddc7610efd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:29:50.146268+00:00
-- url     : https://prove2.me/submissions/03a033ce-4ad5-400c-81cb-c4fe707b705a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hplanar, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2 H hH
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2
      K hcard hplanar hmax
  calc
    H.edgeSet.ncard ≤ K.edgeSet.ncard := Set.ncard_mono hsub
    _ = 3 * Fintype.card V - 6 := hcount
