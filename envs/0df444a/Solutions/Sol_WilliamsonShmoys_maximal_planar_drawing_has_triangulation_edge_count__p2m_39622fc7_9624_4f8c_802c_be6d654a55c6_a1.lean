-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_39622fc7_9624_4f8c_802c_be6d654a55c6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:37:02.646327+00:00
-- url     : https://prove2.me/submissions/ef9dc6aa-e178-4976-8225-afc223f662f6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_e2c996e1_3289_4869_babc_b3655d7efc93_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_insertion_below_triangulation_bound__p2m_e2c996e1_3289_4869_babc_b3655d7efc93_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_bound__p2m_e2c996e1_3289_4869_babc_b3655d7efc93_a1 H hH hV
  have hLower : 3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
    by_contra hNot
    have hSparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
    obtain ⟨K, hHK, hK, hne⟩ :=
      WilliamsonShmoys.planar_edge_insertion_below_triangulation_bound__p2m_e2c996e1_3289_4869_babc_b3655d7efc93_a1 H hH hV hSparse
    exact hne (hMax K hHK hK)
  omega