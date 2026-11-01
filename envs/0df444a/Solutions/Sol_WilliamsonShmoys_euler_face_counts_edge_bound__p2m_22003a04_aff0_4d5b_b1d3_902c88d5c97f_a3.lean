-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_counts_edge_bound__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:40:26.097616+00:00
-- url     : https://prove2.me/submissions/f89f4802-d980-4f6c-a09d-ff72244dcb8f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (edgeCount faceCount : ℕ)
    (hEdges : G.edgeSet.ncard = edgeCount)
    (hEuler : Fintype.card V + faceCount = edgeCount + 2)
    (hFaces : 3 * faceCount ≤ 2 * edgeCount) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  rw [hEdges]
  omega