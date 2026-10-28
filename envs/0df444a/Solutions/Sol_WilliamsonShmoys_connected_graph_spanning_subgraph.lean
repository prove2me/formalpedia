-- Prove2me | solution 1 for WilliamsonShmoys.connected_graph_spanning_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:20:29.90454+00:00
-- url     : https://prove2.me/submissions/4da3e1da-499d-42bf-bb5c-b60ee93187bc

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (hH : H.Connected) :
    ∃ T : SimpleGraph V,
      T.Connected ∧
      (∀ u v, T.Adj u v → H.Adj u v) := by 
  exact ⟨H, hH, fun u v h => h⟩
