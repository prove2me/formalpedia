-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_finite_maximal_extension__p2m_3750f754_8764_46ea_8741_399ac1e39bbe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:53:28.506765+00:00
-- url     : https://prove2.me/submissions/20d0ef52-83aa-47ed-a419-710098747a96

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_f2239872_da14_4fcd_a2f9_08c413d80af1_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by
  have hdown : ∀ ⦃A B : SimpleGraph V⦄,
      A ≤ B → WilliamsonShmoys.HasPlanarDrawingOn B →
        WilliamsonShmoys.HasPlanarDrawingOn A := by
    intro A B hAB hB
    rcases hB with ⟨p, arc, hp, hedge, hcross⟩
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro u v huv hAdj
      exact hedge u v huv (hAB hAdj)
    · intro u v x y huv hxy hAdjuv hAdjxy hedges t ht s hs heq
      exact hcross u v x y huv hxy (hAB hAdjuv) (hAB hAdjxy) hedges t ht s hs heq
  rcases WilliamsonShmoys.finite_maximal_extension__p2m_f2239872_da14_4fcd_a2f9_08c413d80af1_a1
      (P := WilliamsonShmoys.HasPlanarDrawingOn) hdown G hG with
    ⟨H, hGH, hH, hmax⟩
  exact ⟨H, hGH, hH, fun K hHK hK => hmax K hHK hK⟩