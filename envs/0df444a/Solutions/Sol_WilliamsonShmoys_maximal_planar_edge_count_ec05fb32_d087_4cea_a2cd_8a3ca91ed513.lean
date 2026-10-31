-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:52:18.458642+00:00
-- url     : https://prove2.me/submissions/f04a03e5-eff4-4578-9337-06e1caffd2d3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys.planar_edge_upper_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
    N hV hN
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
    N hV hN hmax
  omega