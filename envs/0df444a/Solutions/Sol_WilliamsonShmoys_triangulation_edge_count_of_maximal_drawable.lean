-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_edge_count_of_maximal_drawable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:12:21.238385+00:00
-- url     : https://prove2.me/submissions/7387976d-1393-4921-8619-d713e68ee614

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_has_triangulating_supergraph
import Theorems.Thm_WilliamsonShmoys_drawable_edge_count_upper_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ H : SimpleGraph V, U ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ U) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hUH, hH, hHlower⟩ :=
    WilliamsonShmoys.drawable_has_triangulating_supergraph U hV hU
  have hHU : H ≤ U := hmax H hUH hH
  have hEq : H = U := le_antisymm hHU hUH
  have hLower : 3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
    simpa only [hEq] using hHlower
  have hUpper := WilliamsonShmoys.drawable_edge_count_upper_bound U hV hU
  omega