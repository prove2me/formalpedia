-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_lt_of_le_ne
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:26:54.111319+00:00
-- url     : https://prove2.me/submissions/81d81827-8dd8-4281-be6b-beccff5a1916

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H) (hne : G ≠ H) :
    G.edgeSet.ncard < H.edgeSet.ncard := by
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  refine (Set.ssubset_iff_subset_ne).2 ⟨SimpleGraph.edgeSet_mono hGH, fun h => hne (SimpleGraph.edgeSet_injective h)⟩
