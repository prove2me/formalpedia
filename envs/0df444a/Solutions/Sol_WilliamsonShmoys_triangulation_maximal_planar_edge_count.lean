-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_maximal_planar_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:38:22.151758+00:00
-- url     : https://prove2.me/submissions/b8f43700-c02b-4cb5-8dba-42e748fbf825
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W →
      W.edgeSet.ncard ≤ U.edgeSet.ncard) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hUH, hH, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067 U hV hU
  have hle := hmax H hUH hH
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067 U hV hU
  omega