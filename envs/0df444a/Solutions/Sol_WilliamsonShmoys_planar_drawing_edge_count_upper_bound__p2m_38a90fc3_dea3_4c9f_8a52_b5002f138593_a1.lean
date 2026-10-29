-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_38a90fc3_dea3_4c9f_8a52_b5002f138593_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:26:54.399804+00:00
-- url     : https://prove2.me/submissions/776d7e51-6650-474e-9eeb-0bb5e22c348a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_ef7acfeb_d97d_47d2_a77f_a6410accbe74_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHcard, _hHplanar⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ef7acfeb_d97d_47d2_a77f_a6410accbe74_a1
      G hV hG
  have hle : G.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hGH)
  omega