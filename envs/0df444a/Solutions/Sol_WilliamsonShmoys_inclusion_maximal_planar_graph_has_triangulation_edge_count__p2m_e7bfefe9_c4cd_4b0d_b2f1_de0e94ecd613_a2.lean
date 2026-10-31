-- Prove2me | solution 1 for WilliamsonShmoys.inclusion_maximal_planar_graph_has_triangulation_edge_count__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:56:51.211646+00:00
-- url     : https://prove2.me/submissions/279cbe3b-d10b-452d-ba46-303c11cb38e0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_extension_edge_count__p2m_55ffc515_2d9b_4bf9_8fab_2747393ddd23_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_extension_edge_count__p2m_55ffc515_2d9b_4bf9_8fab_2747393ddd23_a1 H hCard hH
  have hKH : K.edgeSet ⊆ H.edgeSet := hmax K hHK hK
  have hedge : H.edgeSet = K.edgeSet := Set.Subset.antisymm hHK hKH
  rw [hedge]
  exact hcount