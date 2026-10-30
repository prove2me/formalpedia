-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_219c2427_f0ca_410a_8cab_2194ee3f8b9c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:28:58.395222+00:00
-- url     : https://prove2.me/submissions/c81d66d4-a5e2-4c47-9fae-7a9a74aa0cd2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_219c2427_f0ca_410a_8cab_2194ee3f8b9c
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_219c2427_f0ca_410a_8cab_2194ee3f8b9c

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_drawing_edge_count_upper_219c2427_f0ca_410a_8cab_2194ee3f8b9c
      K hK hCard
  · exact WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_219c2427_f0ca_410a_8cab_2194ee3f8b9c
      K hK hCard hMax
