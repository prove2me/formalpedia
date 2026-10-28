-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_f274a542
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:27:26.55441+00:00
-- url     : https://prove2.me/submissions/5ff982e3-0b7d-487f-95af-a9f137f3dde4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨M, hLM, hMdraw, hMcard⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_edge_count L hV hL
  have hML : M = L := hmax M hLM hMdraw
  simpa [hML] using hMcard