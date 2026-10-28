-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_via_drawingOn_282b0fbb
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:17:30.911157+00:00
-- url     : https://prove2.me/submissions/15645f28-51c3-4518-aa48-278813fd6ae4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → M ≤ L) :
    3 * (Fintype.card V : Int) - 6 <= (L.edgeSet.ncard : Int) := by
  obtain ⟨M, hM, hLM, hbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_lower_v2 L hL hCard
  have hML : M ≤ L := hmax M hM hLM
  have hEq : M = L := le_antisymm hML hLM
  simpa [hEq] using hbound