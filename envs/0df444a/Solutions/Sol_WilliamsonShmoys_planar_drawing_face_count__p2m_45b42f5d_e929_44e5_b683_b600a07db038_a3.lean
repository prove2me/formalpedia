-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:12.548209+00:00
-- url     : https://prove2.me/submissions/b649473c-a2bb-41d5-8ac9-2179c034c9a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler__p2m_817efdd6_f4a1_4a63_bdc1_5f87cd74d1d4_a1
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_817efdd6_f4a1_4a63_bdc1_5f87cd74d1d4_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hconn : M.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * M.edgeFinset.card := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler__p2m_817efdd6_f4a1_4a63_bdc1_5f87cd74d1d4_a1
      M hM hconn
  have hEdge :=
    WilliamsonShmoys.planar_simple_edge_bound__p2m_817efdd6_f4a1_4a63_bdc1_5f87cd74d1d4_a1
      M hM hconn hcard
  refine ⟨f, hEuler, ?_⟩
  nlinarith