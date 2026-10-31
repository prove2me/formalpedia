-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:30:02.892479+00:00
-- url     : https://prove2.me/submissions/53e58639-2ecc-4722-93fc-ea7a1ada5f05

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph_of_hereditary__p2m_cf95c127_ee46_41b0_beca_773ede50ca42_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V) :
    ∃ Y : SimpleGraph V, X ≤ Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      ∀ Z : SimpleGraph V, Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y := by
  have hHer : ∀ {A B : SimpleGraph V}, A ≤ B →
      WilliamsonShmoys.HasPlanarDrawingOn B →
      WilliamsonShmoys.HasPlanarDrawingOn A := by
    intro A B hAB hB
    rcases hB with ⟨p, arc, hp, hEdges, hCross⟩
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro u v huv hadj
      exact hEdges u v huv (hAB hadj)
    · intro u v x y huv hxy hadj hxyadj hne t ht s hs heq
      exact hCross u v x y huv hxy (hAB hadj) (hAB hxyadj) hne t ht s hs heq
  exact WilliamsonShmoys.finite_maximal_supergraph_of_hereditary__p2m_cf95c127_ee46_41b0_beca_773ede50ca42_a1
    WilliamsonShmoys.HasPlanarDrawingOn hHer X hX