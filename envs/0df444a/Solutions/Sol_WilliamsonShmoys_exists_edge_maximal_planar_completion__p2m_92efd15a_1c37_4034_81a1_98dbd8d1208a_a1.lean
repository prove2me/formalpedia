-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_completion__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:35:50.450579+00:00
-- url     : https://prove2.me/submissions/dbffab32-73d5-428c-b437-4a593600582a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_finite_property_has_maximal_supergraph__p2m_e39dc392_ef53_43de_92b9_a9ba96581299_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  exact WilliamsonShmoys.finite_property_has_maximal_supergraph__p2m_e39dc392_ef53_43de_92b9_a9ba96581299_a2
    N WilliamsonShmoys.HasPlanarDrawingOn
    (by
      intro A B hAB hB
      rcases hB with ⟨p, arc, hp, hEdges, hCross⟩
      refine ⟨p, arc, hp, ?_, ?_⟩
      · intro u v huv hAdj
        exact hEdges u v huv (hAB hAdj)
      · intro u v x y huv hxy hAdjUV hAdjXY hne t ht s hs hEq
        exact hCross u v x y huv hxy (hAB hAdjUV) (hAB hAdjXY) hne t ht s hs hEq)
    hN