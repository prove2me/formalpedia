-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:59:01.109863+00:00
-- url     : https://prove2.me/submissions/76380e13-11d1-4421-baa8-3cc6c4f2bbd8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      (Fintype.card V : ℤ) - (M.edgeFinset.card : ℤ) + (f : ℤ) = 2 ∧
      3 * f ≤ 2 * M.edgeFinset.card := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_formula__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1
      M hM hconn
  have hedge :=
    WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1
      M hM hconn hcard
  refine ⟨f, heuler, ?_⟩
  omega