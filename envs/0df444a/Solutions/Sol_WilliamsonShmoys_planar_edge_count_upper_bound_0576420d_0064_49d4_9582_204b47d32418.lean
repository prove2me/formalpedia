-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_0576420d_0064_49d4_9582_204b47d32418
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:10:04.063005+00:00
-- url     : https://prove2.me/submissions/9076db0e-d2c2-4acf-a1f2-344cd6d9bc2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_component_planar_edge_bound_from_drawing__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
import Theorems.Thm_WilliamsonShmoys_small_component_edge_bound__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_component_bounds__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  apply WilliamsonShmoys.planar_edge_bound_of_component_bounds__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4 L hCard
  intro C
  constructor
  · intro hlarge
    exact WilliamsonShmoys.component_planar_edge_bound_from_drawing__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
      L hL C hlarge
  · intro hsmall
    exact WilliamsonShmoys.small_component_edge_bound__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4 L C hsmall