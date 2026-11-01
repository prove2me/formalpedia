-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_extension_of_local_step__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:46:03.19528+00:00
-- url     : https://prove2.me/submissions/c8162812-ae40-468a-b8bf-e3eeafa9f95e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_finite_connected_extension_of_local_step__p2m_fd72d2a3_1351_4a08_9062_0054809ba074_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hstep : ∀ (G : SimpleGraph V), K ≤ G → HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  exact finite_connected_extension_of_local_step__p2m_fd72d2a3_1351_4a08_9062_0054809ba074_a1
    K HasPlanarDrawingOn hK hstep