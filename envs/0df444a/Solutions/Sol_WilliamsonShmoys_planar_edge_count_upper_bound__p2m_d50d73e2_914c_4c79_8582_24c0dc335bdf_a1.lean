-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_d50d73e2_914c_4c79_8582_24c0dc335bdf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:33:17.040738+00:00
-- url     : https://prove2.me/submissions/5665ba94-3581-4dfa-8890-1bf8ee7223c3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_fa13a70a_f07b_4cf3_b92f_4d7140819b58_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨N, hmono, hcount, _hDrawN⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_fa13a70a_f07b_4cf3_b92f_4d7140819b58_a1
      K hCard hDraw
  exact hmono.trans (le_of_eq hcount)