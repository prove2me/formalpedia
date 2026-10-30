-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulated_extension_maximal_supergraph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:16:38.414884+00:00
-- url     : https://prove2.me/submissions/b77c2d93-afd1-4076-a55b-f08e5ea66c52

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_edge_upper_bound_51bf81b4_48bc_4660_b9e1_3005ea79cb82
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_edge_lower_bound_51bf81b4_48bc_4660_b9e1_3005ea79cb82

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.maximal_drawable_extension_edge_upper_bound_51bf81b4_48bc_4660_b9e1_3005ea79cb82 M hV hM
  have hlower :=
    WilliamsonShmoys.maximal_drawable_extension_edge_lower_bound_51bf81b4_48bc_4660_b9e1_3005ea79cb82 M hV hM hmax
  omega