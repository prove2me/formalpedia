-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:12:41.903371+00:00
-- url     : https://prove2.me/submissions/73566292-e8c0-444e-a066-22923b9ecfd9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion_edge_count

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L →
      M.edgeSet ⊆ L.edgeSet →
      L.edgeSet ⊆ M.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hL, hML, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_completion_edge_count M hV hM
  have hLM : L.edgeSet ⊆ M.edgeSet := hmax L hL hML
  have hsets : M.edgeSet = L.edgeSet := Set.Subset.antisymm hML hLM
  rw [hsets]
  exact hcount