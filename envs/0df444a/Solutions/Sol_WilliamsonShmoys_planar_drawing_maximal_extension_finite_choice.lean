-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_finite_choice
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:48:41.118982+00:00
-- url     : https://prove2.me/submissions/e0ca485b-2e2e-45e6-b1e0-ad48a8e6b2a9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_hereditary_property_maximal_extension
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V,
        S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S := by
  exact WilliamsonShmoys.finite_hereditary_property_maximal_extension
    (P := WilliamsonShmoys.HasPlanarDrawingOn) (by
      intro G H hHG hG
      rcases hG with ⟨p, arc, hp, hEdges, hCross⟩
      refine ⟨p, arc, hp, ?_, ?_⟩
      · intro u v huv hAdj
        exact hEdges u v huv (hHG hAdj)
      · intro u v x y huv hxy hAdjUV hAdjXY hne t ht s hs heq
        exact hCross u v x y huv hxy (hHG hAdjUV) (hHG hAdjXY) hne t ht s hs heq
    ) R hRdraw