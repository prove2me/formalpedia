-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_b320f89e_6adf_4c95_8da8_b179076388d4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:47.73247+00:00
-- url     : https://prove2.me/submissions/8439232f-58a0-46de-a201-483724749c4c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_set_has_maximal_extension__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2
import Theorems.Thm_WilliamsonShmoys_finite_set_of_planar_drawings__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    exists N : SimpleGraph V,
      M <= N /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      (forall K : SimpleGraph V,
        N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= N) := by
  have hfin : ({N : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn N} : Set (SimpleGraph V)).Finite :=
    WilliamsonShmoys.finite_set_of_planar_drawings__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2 (V := V)
  obtain ⟨N, hN, hMN, hmax⟩ :=
    WilliamsonShmoys.finite_set_has_maximal_extension__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2
      ({N : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn N} : Set (SimpleGraph V))
      hfin M hM
  exact ⟨N, hMN, hN, fun K hNK hK => hmax K hNK hK⟩