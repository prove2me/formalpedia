-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_repair_20261027
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:08:33.905852+00:00
-- url     : https://prove2.me/submissions/f8e3643d-8088-4bc1-9f67-f4a99c139bb2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_dense

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨M, hLM, hMdraw, hbound⟩ :=
    WilliamsonShmoys.planar_completion_dense L hV hdraw
  have hML : M ≤ L := hmax M hLM hMdraw
  have hedge : M.edgeSet ⊆ L.edgeSet :=
    (SimpleGraph.edgeSet_subset_edgeSet).2 hML
  exact le_trans hbound (Set.ncard_le_ncard hedge)