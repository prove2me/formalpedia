-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:19:34.496221+00:00
-- url     : https://prove2.me/submissions/7b8afee5-19ff-4a37-a5ba-a97c0002fbcf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_le_of_drawing
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ge

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ J : SimpleGraph V, K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_le_of_drawing K hDraw hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_ge K hDraw hMax hCard
  omega