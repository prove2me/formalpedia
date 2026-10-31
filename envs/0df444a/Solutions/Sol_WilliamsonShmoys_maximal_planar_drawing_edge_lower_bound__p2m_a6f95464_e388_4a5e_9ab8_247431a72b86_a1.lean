-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:40:40.233711+00:00
-- url     : https://prove2.me/submissions/f42cda81-2077-447a-acbc-035f73108b9b

import Theorems.Thm_WilliamsonShmoys_edge_bound_of_maximal_drawable

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard :=
  WilliamsonShmoys.edge_bound_of_maximal_drawable M hCard hM hMax
