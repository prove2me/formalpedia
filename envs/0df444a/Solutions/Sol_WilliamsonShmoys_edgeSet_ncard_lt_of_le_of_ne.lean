-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_lt_of_le_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:35:28.075089+00:00
-- url     : https://prove2.me/submissions/89141357-71c9-4389-90f0-143fed6883ca

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L M : SimpleGraph V) (hLM : L ≤ M) (hne : M ≠ L) :
    L.edgeSet.ncard < M.edgeSet.ncard := by
  apply Set.ncard_lt_ncard
  · exact SimpleGraph.edgeSet_strict_mono (lt_of_le_of_ne hLM (Ne.symm hne))
  · exact Set.toFinite _