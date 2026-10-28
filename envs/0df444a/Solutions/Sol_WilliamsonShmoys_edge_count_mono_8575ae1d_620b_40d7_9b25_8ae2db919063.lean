-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_mono_8575ae1d_620b_40d7_9b25_8ae2db919063
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:28:26.569436+00:00
-- url     : https://prove2.me/submissions/263248da-08cb-439f-92e0-828c722a6058

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (Q R : SimpleGraph V)
    (hQR : Q ≤ R) :
    Q.edgeSet.ncard ≤ R.edgeSet.ncard :=
  Set.ncard_le_ncard (fun e he => SimpleGraph.edgeSet_mono hQR he) (Set.toFinite _)
