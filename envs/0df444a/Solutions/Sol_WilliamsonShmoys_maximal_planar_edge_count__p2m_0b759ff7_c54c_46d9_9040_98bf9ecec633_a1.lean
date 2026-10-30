-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_edge_count__p2m_0b759ff7_c54c_46d9_9040_98bf9ecec633_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:53:49.7412+00:00
-- url     : https://prove2.me/submissions/4e5b76ab-83b0-4a53-915a-322503ec1d47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_2aad9942_4caf_404d_a0f5_d5621274176b_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_2aad9942_4caf_404d_a0f5_d5621274176b_a1
      H hH hV
  have hEq : H.edgeSet = K.edgeSet := Set.Subset.antisymm hHK (hmax K hHK hK)
  rw [hEq]
  exact hcard