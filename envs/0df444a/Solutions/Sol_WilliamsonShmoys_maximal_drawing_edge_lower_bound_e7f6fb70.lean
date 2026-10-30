-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_lower_bound_e7f6fb70
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:58:57.305137+00:00
-- url     : https://prove2.me/submissions/dcb34ba1-ffaf-4cf6-973a-e491f3195071

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound_e7f6fb70

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : forall Z : SimpleGraph V, Y <= Z ->
      WilliamsonShmoys.HasPlanarDrawingOn Z -> Z = Y) :
    3 * Fintype.card V <= Y.edgeSet.ncard + 6 := by
  obtain ⟨Z, hYZ, hZ, hbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_lower_bound_e7f6fb70 Y hV hY
  have hZY : Z = Y := hmax Z hYZ hZ
  simpa [hZY] using hbound