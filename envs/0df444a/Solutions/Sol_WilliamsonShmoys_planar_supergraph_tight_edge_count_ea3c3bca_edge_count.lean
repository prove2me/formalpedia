-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_tight_edge_count_ea3c3bca_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:52:01.958004+00:00
-- url     : https://prove2.me/submissions/da20a6b0-6d61-4d7d-bbf2-c7ff93ededf5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_v2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L)
    (hcard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := planar_drawable_edge_upper_bound L hL hcard
  have hlower := maximal_planar_edge_lower_bound_v2 L hL hmax hcard
  omega