-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_c14927fd_3bb2_4aa2_8e62_690259e960a9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:02:58.703589+00:00
-- url     : https://prove2.me/submissions/dbc5e287-9c7b-47cb-8409-8f4df1b08321
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_of_disconnected_graph__p2m_8a39e0cf_ef07_4e8d_9689_6d4757ac8893_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.Connected := by
  classical
  by_contra hconn
  obtain ⟨L, hKL, hL, hnot⟩ :=
    WilliamsonShmoys.planar_extension_of_disconnected_graph__p2m_8a39e0cf_ef07_4e8d_9689_6d4757ac8893_a1
      K hcard hK hconn
  exact hnot (hmax L hKL hL)