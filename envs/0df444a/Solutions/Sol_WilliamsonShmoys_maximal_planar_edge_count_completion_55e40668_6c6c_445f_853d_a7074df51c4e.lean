-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_completion_55e40668_6c6c_445f_853d_a7074df51c4e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:32:51.626688+00:00
-- url     : https://prove2.me/submissions/c3b0d1db-0a4b-44b7-9c5f-e5e9f564fbba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_simple_edge_upper_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e L hL hV
  · exact WilliamsonShmoys.maximal_planar_edge_lower_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e L hL hmax hV