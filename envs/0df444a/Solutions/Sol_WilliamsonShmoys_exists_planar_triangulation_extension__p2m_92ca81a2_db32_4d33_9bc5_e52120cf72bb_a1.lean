-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension__p2m_92ca81a2_db32_4d33_9bc5_e52120cf72bb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:57:01.030547+00:00
-- url     : https://prove2.me/submissions/998e4850-7e0d-4900-9c57-a15575dcf214

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V,
      H ≤ G ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel G.Adj := Classical.decRel G.Adj
       H.edgeFinset.card ≤ G.edgeFinset.card ∧
       G.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨G, hHG, hGdraw, hcardMono, hGmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a2 H hHdraw
  have hGedges :=
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a2 G hcard hGdraw hGmax
  exact ⟨G, hHG, hGdraw, ⟨hcardMono, hGedges⟩⟩