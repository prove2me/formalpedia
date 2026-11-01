-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:12:21.375035+00:00
-- url     : https://prove2.me/submissions/99e92c16-a5c2-4cb1-9c6a-49e06e4b4e3b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_count__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * H.edgeFinset.card := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_count__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
      H hH hconn
  have hEdge :=
    WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
      H hH hcard
  refine ⟨f, hEuler, ?_⟩
  omega