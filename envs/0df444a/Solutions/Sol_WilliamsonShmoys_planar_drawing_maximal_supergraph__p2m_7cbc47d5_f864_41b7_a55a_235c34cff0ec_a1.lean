-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_7cbc47d5_f864_41b7_a55a_235c34cff0ec_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:10:59.233913+00:00
-- url     : https://prove2.me/submissions/019347dd-5887-4a6f-96b1-bcf2b448ad9c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_downward_closed__p2m_30147cc2_3609_4f7e_9a97_a6f7a798fcab_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) := by
  have hdown : ∀ ⦃A B : SimpleGraph V⦄,
      A ≤ B → HasPlanarDrawingOn B → HasPlanarDrawingOn A := by
    intro A B hAB hB
    rcases hB with ⟨p, arc, hp, hedge, hcross⟩
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro u v huv hAuv
      exact hedge u v huv (hAB hAuv)
    · intro u v x y huv hxy hAuv hAxy hne t ht s hs heq
      exact hcross u v x y huv hxy (hAB hAuv) (hAB hAxy) hne t ht s hs heq
  exact WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed__p2m_30147cc2_3609_4f7e_9a97_a6f7a798fcab_a1
    HasPlanarDrawingOn hdown G hG