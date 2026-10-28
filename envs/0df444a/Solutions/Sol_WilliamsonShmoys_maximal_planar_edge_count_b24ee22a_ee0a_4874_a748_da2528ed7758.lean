-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_b24ee22a_ee0a_4874_a748_da2528ed7758
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:27:06.559232+00:00
-- url     : https://prove2.me/submissions/12c9531a-4a14-45c9-a490-85b06053742b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_maximal_edge_count
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_lower_edge_bound_for_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  have hUpper : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_bound_for_maximal_edge_count K hK hCard
  have hLower : 3 * Fintype.card V ≤ K.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_drawing_lower_edge_bound_for_exact_edge_count
      K hK hmax hCard
  omega
