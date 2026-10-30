-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:34:14.860839+00:00
-- url     : https://prove2.me/submissions/6a62c4a4-03ed-4b7b-8688-7581073126d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_count__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ J : SimpleGraph V, G ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J →
      J.edgeSet.ncard ≤ G.edgeSet.ncard) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_bound__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1 G hDraw hCard
  obtain ⟨J, hGJ, hJDraw, hJCount⟩ :=
    WilliamsonShmoys.planar_maximal_extension_count__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1 G hDraw hCard
  have hLower := hMax J hGJ hJDraw
  omega