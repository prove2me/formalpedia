-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_strict_of_edgeSet_ncard_lt_20261026
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:59:57.295204+00:00
-- url     : https://prove2.me/submissions/e5db49be-2000-41cd-8ddf-f1d3b9f37076

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (L M : SimpleGraph V)
    (hLM : L ≤ M)
    (hcard : L.edgeSet.ncard < M.edgeSet.ncard) :
    L < M := by
  refine lt_of_le_of_ne hLM ?_
  rintro rfl
  exact lt_irrefl _ hcard
