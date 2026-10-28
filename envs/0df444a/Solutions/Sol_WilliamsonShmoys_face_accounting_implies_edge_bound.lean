-- Prove2me | solution 1 for WilliamsonShmoys.face_accounting_implies_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:27:24.567402+00:00
-- url     : https://prove2.me/submissions/72e7a5a0-0f45-4c28-b3d1-06ad4829ea4c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hData : ∃ (f b : Nat),
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      2 * G.edgeSet.ncard = b ∧
      3 * f ≤ b) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  rcases hData with ⟨f, b, hEuler, hBoundary, hFaces⟩
  omega