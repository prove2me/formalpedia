-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_faceCount_bounds__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:15:33.398676+00:00
-- url     : https://prove2.me/submissions/0e36fe16-d879-48f9-b2bd-10b5b35cd448
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planarDrawing_euler_face_count__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_count_bound__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) (hconn : U.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     ∃ f : Nat,
       Fintype.card V + f = U.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * U.edgeFinset.card) := by
  letI : DecidableRel U.Adj := dU
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planarDrawing_euler_face_count__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
      U dU hU hconn
  have hEdge :=
    WilliamsonShmoys.planarDrawing_edge_count_bound__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
      U dU hU hcard
  refine ⟨f, hEuler, ?_⟩
  omega