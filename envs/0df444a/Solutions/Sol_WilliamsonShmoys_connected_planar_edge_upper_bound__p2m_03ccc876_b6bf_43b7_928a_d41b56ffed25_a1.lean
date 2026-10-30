-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:28:28.086706+00:00
-- url     : https://prove2.me/submissions/75f3960f-d0c1-460a-a41e-ad2f00024e77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_ce9f6242_56a0_4c10_94b5_7a9007787131_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, dH, hsub, _hconnH, _hplanarH, hEq, hmono⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ce9f6242_56a0_4c10_94b5_7a9007787131_a2
      K hK hconn hcard
  letI : DecidableRel H.Adj := dH
  rw [← hEq]
  exact hmono