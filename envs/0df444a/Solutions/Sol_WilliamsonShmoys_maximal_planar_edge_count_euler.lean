-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_euler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:52:17.400727+00:00
-- url     : https://prove2.me/submissions/a5a4054b-9a02-45a4-a9c0-e144640f7756
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_0576420d_0064_49d4_9582_204b47d32418
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_0576420d_0064_49d4_9582_204b47d32418

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound_0576420d_0064_49d4_9582_204b47d32418 L hL hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_0576420d_0064_49d4_9582_204b47d32418 L hL hMax hCard
  omega