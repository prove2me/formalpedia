-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_0d58a30b_b602_48eb_8495_a2236e2d87f2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:33:37.406111+00:00
-- url     : https://prove2.me/submissions/9457727d-98f8-4770-97d1-6b9e7c97a747
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_planar_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_strict_augmentation
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hTdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hTmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  have hUpper := WilliamsonShmoys.maximal_drawable_edge_count_planar_upper_bound
    T hTdraw hCard
  have hLower : 3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
    by_contra h
    have hSparse : T.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
    obtain ⟨U, hTU, hUne, hUdraw⟩ :=
      WilliamsonShmoys.maximal_drawable_edge_count_strict_augmentation T hTdraw hCard hSparse
    have hEq : U = T := hTmax U hTU hUdraw
    exact hUne hEq
  exact Nat.le_antisymm hLower hUpper