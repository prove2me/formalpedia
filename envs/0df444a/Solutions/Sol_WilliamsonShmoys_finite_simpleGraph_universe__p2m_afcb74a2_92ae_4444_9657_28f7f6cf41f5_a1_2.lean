-- Prove2me | solution 2 for WilliamsonShmoys.finite_simpleGraph_universe__p2m_afcb74a2_92ae_4444_9657_28f7f6cf41f5_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:15:32.730762+00:00
-- url     : https://prove2.me/submissions/505f1cf1-70ea-4dd6-b0c1-30cf0ea54f29

import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] :
    (Set.univ : Set (SimpleGraph V)).Finite := by
  exact Set.toFinite _
