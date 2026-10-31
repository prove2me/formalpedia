-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:29:31.526027+00:00
-- url     : https://prove2.me/submissions/670dc6bd-6b9a-4d28-a2fe-7609b15e7f6a

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_c5c6f6ee

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_lower_bound_c5c6f6ee N hV hN hmax
