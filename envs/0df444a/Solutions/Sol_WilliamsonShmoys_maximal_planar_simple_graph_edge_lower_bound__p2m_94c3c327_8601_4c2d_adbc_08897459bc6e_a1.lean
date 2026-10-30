-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:52.882338+00:00
-- url     : https://prove2.me/submissions/1c35d808-86a2-4dbe-aaa1-66c970d0d2b4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_triangulation_edge_count__p2m_b1ccffd4_b471_45dd_901d_142379850b78_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨K, hGK, hKplanar, hKedges⟩ :=
    WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count__p2m_b1ccffd4_b471_45dd_901d_142379850b78_a1
      G hV hG
  have hKG : K = G := hmax K hGK hKplanar
  subst K
  exact le_of_eq hKedges