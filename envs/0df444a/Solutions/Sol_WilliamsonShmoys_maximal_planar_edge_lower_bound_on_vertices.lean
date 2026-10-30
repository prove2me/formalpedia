-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_on_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:21:01.761005+00:00
-- url     : https://prove2.me/submissions/8e1a275d-1036-4d4d-bf2d-698267c9cf04

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L <= M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_drawingOn_triangulation L hV hL
  have hML : M = L := hmax M hLM hM
  rw [hML] at hcount
  omega