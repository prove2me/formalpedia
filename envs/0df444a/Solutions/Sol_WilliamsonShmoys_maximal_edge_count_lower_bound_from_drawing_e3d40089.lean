-- Prove2me | solution 1 for WilliamsonShmoys.maximal_edge_count_lower_bound_from_drawing_e3d40089
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:41:14.88611+00:00
-- url     : https://prove2.me/submissions/79e8dc83-64e3-4af9-b07e-be21320bf7d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_completion
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    3 * Fintype.card V <= G.edgeSet.ncard + 6 := by
  obtain ⟨K, hGK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_completion G hG hcard
  have hKG : K = G := hmax K hGK hK
  subst K
  exact le_of_eq hcount