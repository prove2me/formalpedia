-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_ad420e80
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:32:06.747524+00:00
-- url     : https://prove2.me/submissions/50c234e9-49c6-4354-9825-cf7a97f8ee4e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion_b82980ee

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKDraw, hKCard⟩ :=
    WilliamsonShmoys.planar_drawing_exact_edge_count_completion_b82980ee H hCard hDraw
  have hKH : K.edgeSet ⊆ H.edgeSet := hMax K hHK hKDraw
  have hEq : H.edgeSet = K.edgeSet := Set.Subset.antisymm hHK hKH
  rw [hEq]
  exact hKCard