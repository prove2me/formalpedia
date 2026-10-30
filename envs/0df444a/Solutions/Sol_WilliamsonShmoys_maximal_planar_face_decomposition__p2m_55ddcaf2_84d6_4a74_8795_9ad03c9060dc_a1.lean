-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_55ddcaf2_84d6_4a74_8795_9ad03c9060dc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:14:09.578479+00:00
-- url     : https://prove2.me/submissions/48182732-7665-4dde-9cd7-cecbde75c17e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_3fdb186f_984d_4498_b0e7_7fd2238c7ad7_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by
  have hm := WilliamsonShmoys.maximal_planar_edge_count__p2m_3fdb186f_984d_4498_b0e7_7fd2238c7ad7_a1
    H hH hmax hV
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega