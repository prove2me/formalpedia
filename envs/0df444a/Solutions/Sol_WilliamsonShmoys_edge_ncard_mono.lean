-- Prove2me | solution 1 for WilliamsonShmoys.edge_ncard_mono
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:14:00.296403+00:00
-- url     : https://prove2.me/submissions/a19c5414-2f5e-4f1d-bf61-a42b57815377

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hGH)