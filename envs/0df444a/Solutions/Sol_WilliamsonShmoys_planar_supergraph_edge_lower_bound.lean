-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:06:31.002994+00:00
-- url     : https://prove2.me/submissions/2c349644-89f3-438f-a21e-c013e645c8d2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_on_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_on_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_on_vertices K hV hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_edge_lower_bound_on_vertices L hV hL hmax⟩