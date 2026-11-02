-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_bound_data__p2m_cd539f9d_43c0_4104_8907_5b455d63330b_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:18:27.779171+00:00
-- url     : https://prove2.me/submissions/cfe55adc-5e2f-4f90-b557-bccab48b8e33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_equation_data__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ f : Nat,
       Fintype.card V + f = H.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * H.edgeFinset.card) := by
  classical
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_equation_data__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
      H hconn hH
  have hEdge :=
    WilliamsonShmoys.planar_drawing_edge_bound__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
      H hcard hH
  refine ⟨f, hEuler, ?_⟩
  omega