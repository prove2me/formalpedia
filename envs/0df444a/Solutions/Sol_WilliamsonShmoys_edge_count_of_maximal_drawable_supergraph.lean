-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_drawable_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:53:14.77802+00:00
-- url     : https://prove2.me/submissions/e3489543-c1f0-4225-8d4e-7df316033ef9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_extension_edge_count H hV hH
  have hKH : K = H := hmax K hHK hK
  simpa [hKH] using hcount