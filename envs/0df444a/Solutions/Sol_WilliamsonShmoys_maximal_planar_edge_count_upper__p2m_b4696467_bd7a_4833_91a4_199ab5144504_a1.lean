-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:28:15.83821+00:00
-- url     : https://prove2.me/submissions/97fa05e8-043d-4c76-8d49-07d7de7c3940

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_b865fe19_b86f_4742_89c9_6df3d0fd3be8_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hH⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_b865fe19_b86f_4742_89c9_6df3d0fd3be8_a1
      K hplanar hcard
  have hmono : K.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hsub
  omega