-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulating_supergraph__p2m_a2bdd39c_3a82_41f8_ad95_4704547f58a7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:06:30.077302+00:00
-- url     : https://prove2.me/submissions/e894fd50-c193-4287-9125-c3b18a572964

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_drawing_has_three_n_minus_six_edges__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V, N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
      (letI : DecidableRel P.Adj := Classical.decRel P.Adj
       3 * Fintype.card V = P.edgeFinset.card + 6) := by
  obtain ⟨P, hNP, hP, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1
      N hN hcard
  refine ⟨P, hNP, hP, ?_⟩
  exact WilliamsonShmoys.inclusion_maximal_planar_drawing_has_three_n_minus_six_edges__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1
    P hP hmax hcard