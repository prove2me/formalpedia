-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:54:40.056728+00:00
-- url     : https://prove2.me/submissions/fc5a1272-2d70-4acd-818d-080a520e1668
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_component_join_one_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a2
import Theorems.Thm_WilliamsonShmoys_finite_connected_closure_of_monotone_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  have hstep : ∀ G : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ K : SimpleGraph V,
        G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ K.Reachable u v := by
    intro G hG hnot
    exact WilliamsonShmoys.planar_component_join_one_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a2
      hcard G hG hnot
  obtain ⟨K, hHK, hKconn, hKplanar⟩ :=
    WilliamsonShmoys.finite_connected_closure_of_monotone_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a1
      WilliamsonShmoys.HasPlanarDrawingOn hstep H hH
  exact ⟨K, hHK, hKconn, hKplanar⟩