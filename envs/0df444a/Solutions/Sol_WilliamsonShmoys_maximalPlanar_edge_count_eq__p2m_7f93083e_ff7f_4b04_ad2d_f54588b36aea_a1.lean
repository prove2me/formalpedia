-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanar_edge_count_eq__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:52:47.767034+00:00
-- url     : https://prove2.me/submissions/cad5589c-57a7-4435-a51d-d820fcceaac9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximalPlanar_edge_count_upper_bound__p2m_12371c70_d6b7_41aa_8516_3639658d867c_a2
import Theorems.Thm_WilliamsonShmoys_maximalPlanar_edge_count_lower_bound__p2m_12371c70_d6b7_41aa_8516_3639658d867c_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = N.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  have hUpper :=
    WilliamsonShmoys.maximalPlanar_edge_count_upper_bound__p2m_12371c70_d6b7_41aa_8516_3639658d867c_a2
      N hN hCard
  have hLower :=
    WilliamsonShmoys.maximalPlanar_edge_count_lower_bound__p2m_12371c70_d6b7_41aa_8516_3639658d867c_a2
      N hN hMax hCard
  exact Nat.le_antisymm hLower hUpper