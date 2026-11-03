-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:46:59.271815+00:00
-- url     : https://prove2.me/submissions/5d5ad3ea-d847-4e92-ad5b-aed6b1e2df7f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_completion__p2m_f0aba619_3680_404a_84c1_4b765821e2bd_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmono, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_edge_completion__p2m_f0aba619_3680_404a_84c1_4b765821e2bd_a2
      G hcard hG
  exact hmono.trans_eq hcount