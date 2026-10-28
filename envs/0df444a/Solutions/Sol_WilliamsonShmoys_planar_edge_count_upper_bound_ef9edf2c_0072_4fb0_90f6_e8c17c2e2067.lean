-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:17:14.104746+00:00
-- url     : https://prove2.me/submissions/ddc103f5-7a34-4efd-8f83-9ec18dd0a408
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_44d3f95a_e4af_4a94_b096_ba30239a3f07
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_44d3f95a_e4af_4a94_b096_ba30239a3f07
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_44d3f95a_e4af_4a94_b096_ba30239a3f07

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_maximal_extension_44d3f95a_e4af_4a94_b096_ba30239a3f07 G hV hG
  have hEq := WilliamsonShmoys.maximal_planar_edge_count_44d3f95a_e4af_4a94_b096_ba30239a3f07 H hV hH hMax
  have hCard := WilliamsonShmoys.edgeSet_ncard_mono_44d3f95a_e4af_4a94_b096_ba30239a3f07 G H hGH
  omega