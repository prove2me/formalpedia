-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_of_maximality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:11:41.634995+00:00
-- url     : https://prove2.me/submissions/5585062b-e849-4900-a7a3-2d9cfec5ec09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangular_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet ⊆ L.edgeSet →
      L.edgeSet ⊆ K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hLDrawing, hKL, hLCount⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_triangular_edge_count
      K hDrawing hCard
  have hLK : L.edgeSet ⊆ K.edgeSet := hMax L hLDrawing hKL
  have hEq : K.edgeSet = L.edgeSet := Set.Subset.antisymm hKL hLK
  rw [hEq]
  exact hLCount
