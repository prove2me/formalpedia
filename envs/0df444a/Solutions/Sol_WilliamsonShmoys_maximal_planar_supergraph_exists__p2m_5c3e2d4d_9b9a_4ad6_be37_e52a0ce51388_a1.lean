-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_5c3e2d4d_9b9a_4ad6_be37_e52a0ce51388_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:30:21.391552+00:00
-- url     : https://prove2.me/submissions/7cd8f299-d0dd-4c4f-95b4-1dd3b42d384b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_downward_closed_property__p2m_1df87970_57df_486f_9fe9_1f5bd1c60a90_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V,
        J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J := by
  classical
  have hdown : ∀ {G K : SimpleGraph V}, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
        WilliamsonShmoys.HasPlanarDrawingOn G := by
    intro G K hGK hK
    rcases hK with ⟨p, arc, hp, hArc, hMeet⟩
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro u v huv hAdj
      exact hArc u v huv (hGK hAdj)
    · intro u v x y huv hxy hAdjUV hAdjXY hne t ht s hs hEq
      exact hMeet u v x y huv hxy (hGK hAdjUV) (hGK hAdjXY) hne t ht s hs hEq
  exact WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed_property__p2m_1df87970_57df_486f_9fe9_1f5bd1c60a90_a1
    H WilliamsonShmoys.HasPlanarDrawingOn hDraw hdown