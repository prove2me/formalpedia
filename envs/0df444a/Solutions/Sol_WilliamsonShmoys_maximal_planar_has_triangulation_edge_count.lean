-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_has_triangulation_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:36:04.959288+00:00
-- url     : https://prove2.me/submissions/7af927ab-7d9f-41e3-b665-fe0b512b84e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_edge_count_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hLK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_edge_count_completion
      L hL hV
  have hKL : K = L := hmax K hLK hK
  rw [hKL] at hcount
  exact hcount