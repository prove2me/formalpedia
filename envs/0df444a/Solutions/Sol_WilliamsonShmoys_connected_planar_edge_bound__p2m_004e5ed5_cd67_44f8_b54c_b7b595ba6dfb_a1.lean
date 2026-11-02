-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:00:56.652118+00:00
-- url     : https://prove2.me/submissions/5fe5cb24-b878-4574-9ea4-cfbc1612e709
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawing_faceCount_bounds__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1
import Theorems.Thm_WilliamsonShmoys_nat_euler_face_incidence_edge_bound__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) (hconn : U.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel U.Adj := dU
  obtain ⟨f, heuler, hinc⟩ :=
    WilliamsonShmoys.planarDrawing_faceCount_bounds__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1
      U dU hU hconn hcard
  exact WilliamsonShmoys.nat_euler_face_incidence_edge_bound__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1
    (Fintype.card V) U.edgeFinset.card f hcard heuler hinc