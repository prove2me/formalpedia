-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:27:47.067095+00:00
-- url     : https://prove2.me/submissions/ab772392-4f41-47eb-a9d6-ba3d51471264

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_ws

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N ≤ M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_lower_bound_ws M hM hCard hMax
