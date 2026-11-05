-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_face_count__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:26:40.049239+00:00
-- url     : https://prove2.me/submissions/918ccaf6-fb10-47ab-9bdc-4ed508be3c4c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
set_option linter.unusedVariables false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    ∃ f : ℕ, Fintype.card V + f = N.edgeFinset.card + 2 := by
  classical
  have hle : Fintype.card V ≤ N.edgeFinset.card + 1 := by
    simpa [SimpleGraph.edgeFinset] using hconn.card_vert_le_card_edgeSet_add_one
  refine ⟨N.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega
