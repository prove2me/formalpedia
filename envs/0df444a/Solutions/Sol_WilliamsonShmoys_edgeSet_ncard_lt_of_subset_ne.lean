-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_lt_of_subset_ne
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:16:35.540691+00:00
-- url     : https://prove2.me/submissions/32df4178-bf32-45f7-95aa-20d00f8cbe3e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hsub : Set.Subset G.edgeSet H.edgeSet)
    (hne : G.edgeSet ≠ H.edgeSet) :
    Set.ncard G.edgeSet < Set.ncard H.edgeSet := by
  apply Set.ncard_lt_ncard
  · exact Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  · exact Set.toFinite _