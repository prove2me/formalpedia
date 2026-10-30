-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_extension__p2m_57ba8428_9b4f_42ca_9cfe_16138e676737_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:56:09.185064+00:00
-- url     : https://prove2.me/submissions/9669f982-596a-4473-aa8f-dce538e4a7d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_ncard__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNPlanar, hNMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
      M hM
  exact ⟨N, hMN, hNPlanar,
    WilliamsonShmoys.edge_maximal_planar_ncard__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
      N hCard hNPlanar hNMax⟩
