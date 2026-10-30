-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_card_eq_three_n_sub_six
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:19:25.742016+00:00
-- url     : https://prove2.me/submissions/5ff0b766-8202-4016-97ee-57cd13590df8

import Theorems.Thm_WilliamsonShmoys_exists_planar_maximal_supergraph_on
import Theorems.Thm_WilliamsonShmoys_card_eq_three_n_sub_six_of_planar_maximal

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.exists_planar_maximal_supergraph_on G hV hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.card_eq_three_n_sub_six_of_planar_maximal H hV hH hMax⟩