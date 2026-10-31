-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_5b94020c_9ee6_4950_8133_0664742e8f38_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:41:42.586126+00:00
-- url     : https://prove2.me/submissions/4d9bc625-09e8-4684-b127-d9e310dbf8fe

import Theorems.Thm_WilliamsonShmoys_edge_bound_of_maximal_drawable

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard :=
  WilliamsonShmoys.edge_bound_of_maximal_drawable L hV hL hmax
