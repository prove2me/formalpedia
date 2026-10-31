-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:06:10.953482+00:00
-- url     : https://prove2.me/submissions/abf37f94-2626-407b-923f-1a961c13a321

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_partial_order_has_maximal_above__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_of_finite_vertices__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ G : SimpleGraph V, HasPlanarDrawingOn G → H ≤ G → G ≤ H := by
  letI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simpleGraph_of_finite_vertices__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2
  exact WilliamsonShmoys.finite_partial_order_has_maximal_above__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2
    (fun G : SimpleGraph V => HasPlanarDrawingOn G) K hK