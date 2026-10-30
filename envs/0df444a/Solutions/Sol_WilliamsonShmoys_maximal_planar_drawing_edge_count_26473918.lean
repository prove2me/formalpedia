-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_26473918
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:46:30.969722+00:00
-- url     : https://prove2.me/submissions/7d0215d8-e927-4ebd-869b-6d638c7ce008

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_upper_20f2cea7
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_lower_20f2cea7

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.maximal_drawing_edge_count_upper_20f2cea7 K hKdraw hCard
  have hl := WilliamsonShmoys.maximal_drawing_edge_count_lower_20f2cea7 K hKdraw hCard hmax
  omega