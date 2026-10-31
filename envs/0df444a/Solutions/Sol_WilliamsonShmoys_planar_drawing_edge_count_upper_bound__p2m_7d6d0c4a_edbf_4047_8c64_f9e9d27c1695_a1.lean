-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_7d6d0c4a_edbf_4047_8c64_f9e9d27c1695_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:21:11.628471+00:00
-- url     : https://prove2.me/submissions/ca5dc974-8ba0-4f00-9d34-590bf7e6c905

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_completion__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2
import Theorems.Thm_WilliamsonShmoys_subgraph_edge_count_monotone__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, _hDrawH, hCount⟩ :=
    WilliamsonShmoys.planarDrawing_edge_completion__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2
      G hDraw hV
  calc
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
      WilliamsonShmoys.subgraph_edge_count_monotone__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2
        G H hGH
    _ = 3 * Fintype.card V - 6 := hCount
