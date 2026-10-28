-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_repair_8fa97b2b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:01:38.448136+00:00
-- url     : https://prove2.me/submissions/38e237ff-b578-48c0-9210-7484b6ade6e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ M.edgeSet) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hK, hKcard⟩ :=
    WilliamsonShmoys.planar_drawingOn_triangulation_extension M hV hM
  have hreverse : K.edgeSet ⊆ M.edgeSet := hmax K hsub hK
  have heq : M.edgeSet = K.edgeSet := Set.Subset.antisymm hsub hreverse
  rw [heq, hKcard]