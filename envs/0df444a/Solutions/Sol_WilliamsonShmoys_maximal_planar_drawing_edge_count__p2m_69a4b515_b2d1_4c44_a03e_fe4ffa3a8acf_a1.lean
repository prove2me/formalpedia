-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:54:46.166858+00:00
-- url     : https://prove2.me/submissions/bea90024-f6cd-42d1-bc4c-26c32498edbe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangular_face_count_certificate__p2m_f80cfa01_1746_4a4f_be01_21a16939b3a9_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, heuler, htriangular⟩ :=
    WilliamsonShmoys.triangular_face_count_certificate__p2m_f80cfa01_1746_4a4f_be01_21a16939b3a9_a3
      N hV hN hmax
  omega