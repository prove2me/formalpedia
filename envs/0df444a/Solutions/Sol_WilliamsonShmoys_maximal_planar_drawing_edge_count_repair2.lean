-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_repair2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:34:11.798171+00:00
-- url     : https://prove2.me/submissions/ee9e6d4a-171f-4e42-afa1-db543007ce9a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_repair2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_repair2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ M : SimpleGraph V, N ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ N)
    (hV : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hbound : N.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_drawing_edge_bound_repair2 N hN hV
  by_contra hne
  have hlt : N.edgeSet.ncard < 3 * Fintype.card V - 6 :=
    Nat.lt_of_le_of_ne hbound hne
  obtain ⟨M, hNM, hM⟩ :=
    WilliamsonShmoys.planar_drawing_edge_augmentation_repair2 N hN hV hlt
  exact (not_lt_of_ge (hmax M hNM.le hM)) hNM