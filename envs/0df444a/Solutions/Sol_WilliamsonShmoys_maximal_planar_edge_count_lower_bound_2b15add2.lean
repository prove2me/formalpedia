-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_2b15add2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:06:47.206301+00:00
-- url     : https://prove2.me/submissions/bf16e55c-2028-4f2c-8ac4-cdf02fa52ab4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ H : SimpleGraph V, L ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨H, hLH, hH, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_edge_count L hV hL
  have hEq : H = L := hmax H hLH hH
  rw [← hEq]
  omega