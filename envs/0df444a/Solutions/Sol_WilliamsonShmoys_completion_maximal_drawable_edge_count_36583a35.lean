-- Prove2me | solution 1 for WilliamsonShmoys.completion_maximal_drawable_edge_count_36583a35
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:55:40.899582+00:00
-- url     : https://prove2.me/submissions/c7095089-950c-4277-b6f4-d47a93c51993
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_36583a35
import Theorems.Thm_WilliamsonShmoys_planar_augment_below_triangulation_bound_36583a35

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_36583a35 K hK hCard
  by_contra hne
  have hbelow :
      (K.edgeSet.ncard : Int) <
        3 * (Fintype.card V : Int) - 6 :=
    lt_of_le_of_ne hupper hne
  obtain ⟨L, hKL, hStrict, hL⟩ :=
    WilliamsonShmoys.planar_augment_below_triangulation_bound_36583a35
      K hK hCard hbelow
  exact hStrict (hMax L hKL hL)