-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_9dbc1b44_5e81_4cbc_9338_84418c6013a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:56:30.727922+00:00
-- url     : https://prove2.me/submissions/40313035-afee-46eb-9438-a856fdd10a3b

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) :
    (G.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) := by
  exact_mod_cast Set.ncard_le_ncard
    (SimpleGraph.edgeSet_subset_edgeSet.mpr fun _ _ h => hGH h) (Set.toFinite _)
