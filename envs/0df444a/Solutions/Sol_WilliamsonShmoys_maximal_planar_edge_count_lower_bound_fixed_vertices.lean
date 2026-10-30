-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fixed_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:56:05.411494+00:00
-- url     : https://prove2.me/submissions/83d539c1-8494-4624-adf3-93ffa0353386

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_triangulation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMdraw, hMmax, hMcount⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_triangulation L hV hDraw
  have hML : M = L := hmax M hLM hMdraw
  subst M
  omega