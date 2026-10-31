-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulating_supergraph__p2m_e59a889d_669c_414e_8ddd_df780e6fdba8_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:14:39.237532+00:00
-- url     : https://prove2.me/submissions/9fc89903-2728-41d5-98b0-9abced0923fa

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_ff749fca_dc51_4e6e_b241_1d544557ca96_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_ff749fca_dc51_4e6e_b241_1d544557ca96_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hV : 3 ≤ Fintype.card V) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      Z.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Z, hYZ, hZ, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_ff749fca_dc51_4e6e_b241_1d544557ca96_a1
      Y hY
  exact ⟨Z, hYZ, hZ,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ff749fca_dc51_4e6e_b241_1d544557ca96_a1
      Z hZ hV hmax⟩