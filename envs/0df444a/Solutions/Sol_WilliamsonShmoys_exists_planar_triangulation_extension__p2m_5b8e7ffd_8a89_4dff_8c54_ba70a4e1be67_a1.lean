-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension__p2m_5b8e7ffd_8a89_4dff_8c54_ba70a4e1be67_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:51:01.019752+00:00
-- url     : https://prove2.me/submissions/ed183f3a-2702-4d92-a495-30cce553470a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V, G ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
      W.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨W, hGW, hW, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1 G hG
  exact ⟨W, hGW, hW,
    WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1 W hW hmax hV⟩