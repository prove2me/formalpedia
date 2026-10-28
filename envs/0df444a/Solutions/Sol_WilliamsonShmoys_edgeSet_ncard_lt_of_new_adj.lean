-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_lt_of_new_adj
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:53:55.922514+00:00
-- url     : https://prove2.me/submissions/37d7fc0f-2645-41da-a98a-4481809d808d

import Mathlib
theorem solution
    {V : Type} [Fintype V]
    (M N : SimpleGraph V)
    (hsub : ∀ u v, M.Adj u v → N.Adj u v)
    (u v : V)
    (hnew : N.Adj u v)
    (hmissing : ¬ M.Adj u v) :
    M.edgeSet.ncard < N.edgeSet.ncard := by
  have hle : M ≤ N := fun a b h => hsub a b h
  have hss : M.edgeSet ⊂ N.edgeSet := by
    refine ⟨SimpleGraph.edgeSet_mono hle, fun h => hmissing ?_⟩
    exact h (show s(u, v) ∈ N.edgeSet from hnew)
  exact Set.ncard_lt_ncard hss (Set.toFinite _)
