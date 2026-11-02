-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_face_certificate__p2m_b5c387cc_fe7e_4039_9011_ee95aed75dd4_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:40:37.292983+00:00
-- url     : https://prove2.me/submissions/69426659-510a-45ed-a6ac-8081032394d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_formula__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * H.edgeFinset.card := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.connected_planar_euler_formula__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2
      H hH hconn
  have hedge :=
    WilliamsonShmoys.simple_planar_edge_bound__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2
      H hH hcard
  refine ⟨f, heuler, ?_⟩
  omega