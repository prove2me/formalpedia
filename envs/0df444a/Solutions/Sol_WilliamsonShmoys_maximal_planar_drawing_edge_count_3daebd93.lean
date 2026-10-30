-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_3daebd93
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:29:48.041807+00:00
-- url     : https://prove2.me/submissions/779a4831-d8c1-4f55-81e2-392660477e86

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_3daebd93
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_3daebd93

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> K = L) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  exact Nat.le_antisymm
    (WilliamsonShmoys.planar_edge_upper_bound_3daebd93 K hV hK)
    (WilliamsonShmoys.maximal_planar_edge_lower_bound_3daebd93 K hV hK hMax)