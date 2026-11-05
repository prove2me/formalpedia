-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:58:36.770961+00:00
-- url     : https://prove2.me/submissions/2ff66302-ee61-4d97-96d8-aa7e9881d003

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hNH, hHplanar, hNcard, hHmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
      N hN
  have hHcount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
      H hV hHplanar hHmax
  omega