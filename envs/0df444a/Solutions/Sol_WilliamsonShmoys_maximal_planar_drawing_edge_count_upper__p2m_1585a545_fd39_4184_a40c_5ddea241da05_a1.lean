-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_upper__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:20:51.992236+00:00
-- url     : https://prove2.me/submissions/3c995289-be96-4df2-b214-51187c854a9c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_bound__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨M, hGM, hMdraw, hcard, hMmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_bound__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5
      G hG
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hMcount :=
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5
      M hMdraw hV hMmax
  omega