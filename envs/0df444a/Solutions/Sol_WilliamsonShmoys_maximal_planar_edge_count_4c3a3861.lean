-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_4c3a3861
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:44:15.997036+00:00
-- url     : https://prove2.me/submissions/638469f5-d8a0-4280-9ec8-25530f160afb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671 K hK hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671 K hK hCard hmax
  omega