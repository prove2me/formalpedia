-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_drawing_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:21:27.567839+00:00
-- url     : https://prove2.me/submissions/bce350f0-6e6f-48e0-b9b3-d2502209fcab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_edge_count_lower_bound
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  have hlo : 3 * Fintype.card V ≤ K.edgeSet.ncard + 6 :=
    WilliamsonShmoys.edge_maximal_planar_drawing_edge_count_lower_bound K hK hcard hmax
  have hup : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.edge_maximal_planar_drawing_edge_count_upper_bound K hK hcard
  exact Nat.le_antisymm hlo hup