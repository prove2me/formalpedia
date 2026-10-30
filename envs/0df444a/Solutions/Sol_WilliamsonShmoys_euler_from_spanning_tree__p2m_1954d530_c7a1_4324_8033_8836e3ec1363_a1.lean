-- Prove2me | solution 1 for WilliamsonShmoys.euler_from_spanning_tree__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:42:58.723651+00:00
-- url     : https://prove2.me/submissions/5f2f951d-4a19-4053-a887-b7a2a20cdf3e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H T : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hsub : T ≤ H)
    (hTconnected : T.Connected)
    (hTcard : T.edgeSet.ncard + 1 = Fintype.card V) :
    ∃ F : ℕ, Fintype.card V + F = H.edgeSet.ncard + 2 := by
  have hEdges : T.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_subset_edgeSet.mpr hsub)
  refine ⟨H.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega