-- Prove2me | solution 1 for WilliamsonShmoys.supergraph_connected_edge_count_9064c577
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:55:46.642476+00:00
-- url     : https://prove2.me/submissions/62e14e00-752c-4743-84f3-e850d0b493c8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hConn : H.Connected)
    (hHK : ∀ ⦃u v⦄, H.Adj u v → K.Adj u v) :
    K.Connected ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  have hle : H ≤ K := fun u v h => hHK h
  refine ⟨hConn.mono hle, ?_⟩
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hle) (Set.toFinite _)
