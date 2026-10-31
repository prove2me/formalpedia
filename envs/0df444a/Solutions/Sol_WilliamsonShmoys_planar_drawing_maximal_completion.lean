-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_completion
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:59:51.390239+00:00
-- url     : https://prove2.me/submissions/80e291ca-b98a-4959-b451-575fbac5d731

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_completion_for_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard :=
  WilliamsonShmoys.planar_drawing_maximal_completion_for_edge_bound M hV hM
