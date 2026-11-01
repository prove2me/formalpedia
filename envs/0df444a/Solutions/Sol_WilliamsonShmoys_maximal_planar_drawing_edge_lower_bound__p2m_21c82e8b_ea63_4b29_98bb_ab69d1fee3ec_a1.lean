-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_21c82e8b_ea63_4b29_98bb_ab69d1fee3ec_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:41:20.969219+00:00
-- url     : https://prove2.me/submissions/46072989-e883-4e05-bf90-564260748b22
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_edge_lower_bound__p2m_0ac110bd_aaad_4255_8185_0d10e2119357_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hsub, hK, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_triangulated_supergraph_edge_lower_bound__p2m_0ac110bd_aaad_4255_8185_0d10e2119357_a1
      H hcard hH
  have hKH : K = H := hmax K hsub hK
  simpa [hKH] using hbound