-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:20:39.479032+00:00
-- url     : https://prove2.me/submissions/fce8019e-5b84-42b9-a9b6-df513a6aadb0

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) (hKH : K ≤ H) :
    K.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hKH) (Set.toFinite _)
