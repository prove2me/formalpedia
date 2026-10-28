-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_e02108dc_5749_4b8c_85cc_e86e3f71cac7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:43:31.054642+00:00
-- url     : https://prove2.me/submissions/98e3d9f1-b366-4e3c-80e4-de3f0fc2dd3f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_upper_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b
    L hLdraw hCard
  have hLower := WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b
    L hLdraw hCard hMax
  omega