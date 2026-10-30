-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_edge_bound__p2m_d62f521f_25cd_4ab7_9962_c745608392d5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:03:58.021901+00:00
-- url     : https://prove2.me/submissions/1c13600e-c3e0-48a8-b483-f572aca697d4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_ffbccb21_453c_4aae_b4fb_4ee36a71a8e5_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar__p2m_ffbccb21_453c_4aae_b4fb_4ee36a71a8e5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hDraw : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧ HasPlanarDrawingOn H ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hNH, hDrawH, hEdgeCount⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ffbccb21_453c_4aae_b4fb_4ee36a71a8e5_a1
      N hDraw
  have hMaximal : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
    intro K hHK hDrawK
    exact hEdgeCount.2 K hHK hDrawK
  have hExact :=
    WilliamsonShmoys.edge_count_of_maximal_planar__p2m_ffbccb21_453c_4aae_b4fb_4ee36a71a8e5_a1
      H hDrawH hV hMaximal
  exact ⟨H, hNH, hDrawH, hEdgeCount.1, hExact⟩