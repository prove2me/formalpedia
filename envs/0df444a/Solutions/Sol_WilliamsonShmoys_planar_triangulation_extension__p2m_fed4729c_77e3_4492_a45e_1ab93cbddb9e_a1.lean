-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_fed4729c_77e3_4492_a45e_1ab93cbddb9e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:28:27.932628+00:00
-- url     : https://prove2.me/submissions/796fb4ba-144a-41f9-8a0e-0ceb3c4d0b2f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLplanar, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
      K hplanar
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
      L hLplanar hV hmax
  exact ⟨L, hKL, hLplanar, hcount⟩