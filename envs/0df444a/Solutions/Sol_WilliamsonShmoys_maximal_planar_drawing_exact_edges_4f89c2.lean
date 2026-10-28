-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edges_4f89c2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:16:10.384059+00:00
-- url     : https://prove2.me/submissions/b67af678-56ce-428d-b201-b66796f737de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edges_4f89c2_planar_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edges_4f89c2_maximal_planar_edge_count_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ S : SimpleGraph V, R.edgeSet ⊂ S.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn S) :
    R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_planar_drawing_exact_edges_4f89c2_planar_edge_count_upper_bound R hV hR
  · exact WilliamsonShmoys.maximal_planar_drawing_exact_edges_4f89c2_maximal_planar_edge_count_lower_bound R hV hR hmax