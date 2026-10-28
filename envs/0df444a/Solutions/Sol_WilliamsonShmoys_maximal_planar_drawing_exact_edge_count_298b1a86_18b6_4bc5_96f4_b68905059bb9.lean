-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_298b1a86_18b6_4bc5_96f4_b68905059bb9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:22:39.597029+00:00
-- url     : https://prove2.me/submissions/fa82f5fe-6a0a-4bd9-b760-49945f0fd24b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound_298b1a86_18b6_4bc5_96f4_b68905059bb9
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_298b1a86_18b6_4bc5_96f4_b68905059bb9

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  have hUpper := WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound_298b1a86_18b6_4bc5_96f4_b68905059bb9
    N hNdraw hCard
  have hLower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_298b1a86_18b6_4bc5_96f4_b68905059bb9
    N hNdraw hCard hMax
  omega