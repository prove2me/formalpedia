-- Prove2me | solution 1 for SimpleGraph.edgeSet_ncard_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:28.725681+00:00
-- url     : https://prove2.me/submissions/ef404c33-4edf-47af-beb6-7103c2391319

import Mathlib
theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
