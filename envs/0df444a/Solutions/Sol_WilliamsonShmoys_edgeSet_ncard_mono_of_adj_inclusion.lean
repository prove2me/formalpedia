-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_of_adj_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:39:08.752981+00:00
-- url     : https://prove2.me/submissions/4d097f79-2d6c-4e25-89d1-1673a5afa2a3

import Mathlib
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hsub : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono (fun _ _ h => hsub h)) (Set.toFinite _)
end WilliamsonShmoys

