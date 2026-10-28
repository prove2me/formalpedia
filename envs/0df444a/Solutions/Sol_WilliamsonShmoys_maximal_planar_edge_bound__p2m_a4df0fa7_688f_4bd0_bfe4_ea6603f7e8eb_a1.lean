-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:07:04.845424+00:00
-- url     : https://prove2.me/submissions/adef7cb9-2994-4eb6-ae28-6985c4a39e76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound__p2m_46c30075_4bfd_440f_9130_4a3c3cfebadb_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      P.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ P.edgeSet) :
    P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_drawingOn_edge_bound__p2m_46c30075_4bfd_440f_9130_4a3c3cfebadb_a1
    P hP hCard