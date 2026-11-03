-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulation_extension__p2m_5f13f5bc_06ce_43c4_9feb_29baebe6cd36_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:33:47.503266+00:00
-- url     : https://prove2.me/submissions/e7d4a32f-71aa-458f-a267-434a2d7b4853

import Theorems.Thm_WilliamsonShmoys_drawable_graph_maximal_drawable_extension__p2m_ee01e952_1ee0_4062_a12a_4c7920469f52_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count__p2m_ee01e952_1ee0_4062_a12a_4c7920469f52_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G) (hcard : 3 <= Fintype.card V) :
    Exists fun M : SimpleGraph V => Exists fun hDec : DecidableRel M.Adj =>
      letI : DecidableRel M.Adj := hDec
      G <= M /\ HasPlanarDrawingOn M /\ 3 * Fintype.card V = M.edgeFinset.card + 6 := by
  obtain ⟨M, hGM, hM, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_maximal_drawable_extension__p2m_ee01e952_1ee0_4062_a12a_4c7920469f52_a1 G hG
  let hDec : DecidableRel M.Adj := Classical.decRel _
  refine ⟨M, hDec, ?_⟩
  letI : DecidableRel M.Adj := hDec
  refine ⟨hGM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count__p2m_ee01e952_1ee0_4062_a12a_4c7920469f52_a1 M hcard hM hmax