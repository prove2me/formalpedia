-- Prove2me | solution 1 for WilliamsonShmoys.edge_ncard_mono_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T03:21:57.412862+00:00
-- url     : https://prove2.me/submissions/55ad7d42-3031-4ea0-9473-2fae603a11eb

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    (G.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) := by
  exact_mod_cast Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hGH) (Set.toFinite _)
