-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:02:21.798305+00:00
-- url     : https://prove2.me/submissions/b0ca13be-6a2e-4a77-94c3-ff88884680c1

import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N :=
  WilliamsonShmoys.planar_maximal_extension__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1 M hCard hM
