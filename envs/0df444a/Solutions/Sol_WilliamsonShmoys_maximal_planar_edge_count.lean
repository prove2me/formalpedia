-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:27:10.926991+00:00
-- url     : https://prove2.me/submissions/1dbc51b8-eb21-451b-ab22-947b486c5ced

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_upper_bound L hL hV
  have hlo : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound L hL hV hmax
  omega