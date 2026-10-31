-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:37:32.43763+00:00
-- url     : https://prove2.me/submissions/5bef2859-75fd-483a-9f3a-4c153a8081ea

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_dense_extension__p2m_dc333b6e_8abf_48c5_ac8f_62c976c7967e_a2
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hDraw : HasPlanarDrawingOn P)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P) :
    3 * Fintype.card V ≤ P.edgeSet.ncard + 6 := by
  obtain ⟨Q, hPQ, hQDraw, hQBound⟩ :=
    WilliamsonShmoys.planar_drawing_has_dense_extension__p2m_dc333b6e_8abf_48c5_ac8f_62c976c7967e_a2
      P hDraw hV
  have hQP : Q ≤ P := hMax Q hPQ hQDraw
  have hCard : Q.edgeSet.ncard ≤ P.edgeSet.ncard := by
    exact Set.ncard_mono (SimpleGraph.edgeSet_mono hQP)
  omega