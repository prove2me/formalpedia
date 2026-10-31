-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_105a7e64_a154_40f8_8dae_11517fa32419_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:12:29.102401+00:00
-- url     : https://prove2.me/submissions/4534cd64-53b2-4f3a-be36-f52ed1057afb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
      G hG hV
  exact ⟨K, hGK, hKdraw,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
      K hKdraw hV hKmax⟩