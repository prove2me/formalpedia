-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension_edge_count_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:27:49.722274+00:00
-- url     : https://prove2.me/submissions/ff926e5b-b8ff-4aae-88a4-f8982f52ebf2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, W.edgeSet ⊆ X.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn X → X.edgeSet ⊆ W.edgeSet) :
    3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by
  obtain ⟨X, hsub, hX, hbound⟩ :=
    WilliamsonShmoys.planar_augmentation_edge_count_lower_bound W hV hW
  have heq : X.edgeSet = W.edgeSet := Set.Subset.antisymm (hmax X hsub hX) hsub
  simpa [heq] using hbound