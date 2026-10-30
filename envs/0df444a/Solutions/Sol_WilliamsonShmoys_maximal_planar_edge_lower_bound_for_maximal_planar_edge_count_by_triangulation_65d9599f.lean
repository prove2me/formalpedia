-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:05:48.442584+00:00
-- url     : https://prove2.me/submissions/0e18b89f-5238-4bcc-99e3-c4332aa425e8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_from_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ H' : SimpleGraph V,
      H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_supergraph_from_drawing H hV hH
  have hKH : K = H := hmax K hHK hK
  rw [hKH] at hcount
  calc
    3 * Fintype.card V = H.edgeSet.ncard + 6 := hcount
    _ ≤ H.edgeSet.ncard + 6 := le_rfl