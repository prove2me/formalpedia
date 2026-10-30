-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:20:52.101043+00:00
-- url     : https://prove2.me/submissions/ba8279a2-7546-4091-90e6-2d59724dc1ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_connected__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  obtain ⟨M, hKM, hDrawM, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1 K hK
  have hConn :=
    WilliamsonShmoys.maximal_drawable_supergraph_connected__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1
      M hDrawM hV hMax
  exact ⟨M, hKM, hConn, hDrawM⟩