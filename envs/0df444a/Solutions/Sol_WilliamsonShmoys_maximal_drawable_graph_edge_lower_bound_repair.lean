-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_repair
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:04:46.153727+00:00
-- url     : https://prove2.me/submissions/2354594f-4814-43c1-98d4-136fe6ab5b97

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count_repair

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨T, hLT, hT, hcount⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_repair L hV hL
  have hTL : T = L := hmax T hLT hT
  rw [hTL] at hcount
  omega