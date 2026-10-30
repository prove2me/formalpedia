-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_to_triangulation__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:24:42.7519+00:00
-- url     : https://prove2.me/submissions/f1fa93ca-e23e-4af6-a057-263cfd0e432d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_to_maximal_drawable_supergraph__p2m_f6fbb2eb_cab6_4ebc_b0c8_9e00fa476533_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count__p2m_f6fbb2eb_cab6_4ebc_b0c8_9e00fa476533_a2
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hGM, hMDraw, hMax⟩ :=
    WilliamsonShmoys.planar_extension_to_maximal_drawable_supergraph__p2m_f6fbb2eb_cab6_4ebc_b0c8_9e00fa476533_a2
      G hCard hDraw
  refine ⟨M, hGM, hMDraw, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count__p2m_f6fbb2eb_cab6_4ebc_b0c8_9e00fa476533_a2
    M hCard hMDraw hMax