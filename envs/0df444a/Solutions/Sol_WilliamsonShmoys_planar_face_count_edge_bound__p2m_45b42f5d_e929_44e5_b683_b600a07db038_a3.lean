-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_edge_bound__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:29:25.769623+00:00
-- url     : https://prove2.me/submissions/c8ae03f0-139e-4ce1-99d5-ec6439b08aae

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hfaces : ∃ f : ℕ, Fintype.card V + f = M.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * M.edgeFinset.card) :
    M.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  rcases hfaces with ⟨f, heuler, hdegree⟩
  omega