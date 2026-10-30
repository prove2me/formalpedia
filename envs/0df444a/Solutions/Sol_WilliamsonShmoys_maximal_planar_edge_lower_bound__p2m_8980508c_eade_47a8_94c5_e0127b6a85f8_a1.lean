-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:25:17.524971+00:00
-- url     : https://prove2.me/submissions/39dbd706-db61-48df-8bf0-195f4ebced87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_d4833247_a107_430f_bfde_1b2cd697853a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ H' : SimpleGraph V,
      Set.Subset H.edgeSet H'.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn H' →
      H'.edgeSet = H.edgeSet) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨T, hsub, hTdraw, hTcard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_d4833247_a107_430f_bfde_1b2cd697853a_a1
      H hV hdraw
  have heq : T.edgeSet = H.edgeSet := hmax T hsub hTdraw
  rw [← heq]
  omega
