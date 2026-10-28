-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:46:34.941071+00:00
-- url     : https://prove2.me/submissions/43878dea-867c-442b-b452-215ffbb45c21
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_of_planar_drawing

set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨M, hLM, hMdraw, hbound⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_supergraph_of_planar_drawing
      L hV hL
  have hML : M ≤ L := hmax M hLM hMdraw
  have hEq : M = L := le_antisymm hML hLM
  simpa [hEq] using hbound