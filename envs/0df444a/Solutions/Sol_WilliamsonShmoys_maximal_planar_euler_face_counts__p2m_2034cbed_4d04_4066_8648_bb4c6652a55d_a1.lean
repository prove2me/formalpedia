-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_face_counts__p2m_2034cbed_4d04_4066_8648_bb4c6652a55d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:49:25.323911+00:00
-- url     : https://prove2.me/submissions/8df60b7a-094e-46b9-9676-6449e954e07c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ead8e70c_0f57_40e4_8a7a_12724552c1e7_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    ∃ f : ℕ,
      f + Fintype.card V = N.edgeFinset.card + 2 ∧
      3 * f = 2 * N.edgeFinset.card := by
  have hedge := WilliamsonShmoys.maximal_planar_edge_count__p2m_ead8e70c_0f57_40e4_8a7a_12724552c1e7_a1
    N hN hcard hmax
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega