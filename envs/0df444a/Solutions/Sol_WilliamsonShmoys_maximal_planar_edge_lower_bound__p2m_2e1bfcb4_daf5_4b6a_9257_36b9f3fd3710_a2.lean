-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_2e1bfcb4_daf5_4b6a_9257_36b9f3fd3710_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:51:50.481866+00:00
-- url     : https://prove2.me/submissions/db22823c-ac30-4de3-99cb-08efa506d674
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawable_has_lower_bound_supergraph__p2m_669e4dc4_1d9e_4965_8c14_0e14e949cb06_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hMax : ∀ N : SimpleGraph V, G ≤ N → HasPlanarDrawingOn N → N = G)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨H, hGH, hH, hBound⟩ :=
    WilliamsonShmoys.planar_drawable_has_lower_bound_supergraph__p2m_669e4dc4_1d9e_4965_8c14_0e14e949cb06_a1
      G hG hCard
  have hEq : H = G := hMax H hGH hH
  rw [hEq] at hBound
  exact hBound