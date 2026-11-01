-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_data__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:03.416+00:00
-- url     : https://prove2.me/submissions/574b9a7a-76c1-4cf5-b8bf-ae1d42b26a6b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_ce11034e_9d40_4f95_bd08_a8f0a5d53ed0_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_ce11034e_9d40_4f95_bd08_a8f0a5d53ed0_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : Nat, Fintype.card V + f = M.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * M.edgeFinset.card := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_formula__p2m_ce11034e_9d40_4f95_bd08_a8f0a5d53ed0_a1
      M hM hconn
  have hEdge :=
    WilliamsonShmoys.planar_edge_bound__p2m_ce11034e_9d40_4f95_bd08_a8f0a5d53ed0_a1
      M hM hconn hcard
  refine ⟨f, hEuler, ?_⟩
  nlinarith