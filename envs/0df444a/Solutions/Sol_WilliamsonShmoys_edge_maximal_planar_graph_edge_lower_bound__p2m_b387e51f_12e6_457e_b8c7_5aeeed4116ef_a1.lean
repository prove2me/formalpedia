-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_edge_lower_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:36.723904+00:00
-- url     : https://prove2.me/submissions/6a5d1b2b-e69a-433b-9608-35700d2e97ec

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph__p2m_3a9c85e5_093c_48f7_b644_f83c4d4db2f4_a2
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hMax : forall K : SimpleGraph V, G <= K -> HasPlanarDrawingOn K -> K = G) :
    3 * Fintype.card V <= G.edgeSet.ncard + 6 := by
  obtain ⟨K, hGK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_3a9c85e5_093c_48f7_b644_f83c4d4db2f4_a2
      G hV hG
  have hKG : K = G := hMax K hGK hKplanar
  simpa [hKG] using le_of_eq hKcount.symm