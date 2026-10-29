-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_le_of_edge_maximal_planar_c61b3391
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:35:58.967447+00:00
-- url     : https://prove2.me/submissions/ed4b3361-b273-4e29-a937-dceaa30de824

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_extension_for_edge_bound_c61b3391

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_extension_for_edge_bound_c61b3391 H hV hH
  have hKH : K = H := hmax K hHK hK
  simpa [hKH] using le_of_eq hcard