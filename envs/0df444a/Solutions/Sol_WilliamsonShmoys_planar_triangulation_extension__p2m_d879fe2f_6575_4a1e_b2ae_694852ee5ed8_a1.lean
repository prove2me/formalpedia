-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:45:49.711535+00:00
-- url     : https://prove2.me/submissions/6b5f9d70-e140-44c4-ba02-f31e8a303fc7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2
      M hM hCard
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2
      N hN hCard hmax
  exact ⟨N, hMN, hN, hmax, hcount⟩