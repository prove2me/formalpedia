-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_has_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:02:49.476518+00:00
-- url     : https://prove2.me/submissions/c38d382d-4155-4024-aab6-fb5a471c70e8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :
      K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_exact_edge_count_upper_bound
      K hDrawing hCard
  have hLower :
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_exact_edge_count_lower_bound
      K hDrawing hCard hMax
  omega