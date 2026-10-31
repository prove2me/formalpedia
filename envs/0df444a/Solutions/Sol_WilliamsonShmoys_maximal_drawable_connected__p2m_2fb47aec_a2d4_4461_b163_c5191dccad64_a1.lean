-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_connected__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:25:57.354375+00:00
-- url     : https://prove2.me/submissions/474622d3-782e-4196-9e71-a7edcfa230a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_extension__p2m_3e4841aa_5cc8_43c5_ada3_9b4132733a6e_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ H : SimpleGraph V, L ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L)
    (hV : 3 ≤ Fintype.card V) :
    L.Connected := by
  classical
  by_contra hDisconnected
  obtain ⟨H, hLH, hH, hNotSub⟩ :=
    WilliamsonShmoys.disconnected_planar_extension__p2m_3e4841aa_5cc8_43c5_ada3_9b4132733a6e_a2
      L hL hDisconnected hV
  exact hNotSub (hMax H hLH hH)