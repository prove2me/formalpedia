-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_count_upper_20f2cea7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:28:38.590981+00:00
-- url     : https://prove2.me/submissions/76c384b4-75a5-44c9-8a14-16c889ce2b51
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_ge3_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, hHdraw, hHconn⟩ :=
    WilliamsonShmoys.planar_connected_supergraph_ge3_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
      K hKdraw hCard
  have hHbound :=
    WilliamsonShmoys.planar_connected_edge_bound_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
      H hHdraw hHconn hCard
  have hmono :=
    WilliamsonShmoys.edgeSet_ncard_mono_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4 K H hKH
  omega