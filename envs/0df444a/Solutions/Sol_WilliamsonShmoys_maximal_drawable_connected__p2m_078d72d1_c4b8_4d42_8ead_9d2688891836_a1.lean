-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_connected__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:49:59.0892+00:00
-- url     : https://prove2.me/submissions/cae3d3d1-fc4d-4505-a4b9-44d2a8345a66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_extension__p2m_46bd3770_49b2_4c1a_90e5_69dd719cc31d_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.Connected := by
  by_contra hconn
  obtain ⟨x, y, L, hxy, hnotAdj, hKL, hAdj, hL⟩ :=
    WilliamsonShmoys.planar_drawing_disconnected_extension__p2m_46bd3770_49b2_4c1a_90e5_69dd719cc31d_a1
      K hcard hK hconn
  have hLK : L <= K := hmax L hKL hL
  exact hnotAdj (hLK hAdj)