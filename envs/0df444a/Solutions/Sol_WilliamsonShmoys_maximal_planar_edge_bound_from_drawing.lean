-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_from_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:58:57.273986+00:00
-- url     : https://prove2.me/submissions/5254cedf-3b05-4fa7-bacb-cc18f3bd2458
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_edge_bound_6c2b7c10

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hNmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨P, hNP, hPdraw, hPbound⟩ :=
    WilliamsonShmoys.planar_drawing_supergraph_edge_bound_6c2b7c10 N hV hNdraw
  have hPN : P = N := hNmax P hNP hPdraw
  rw [← hPN]
  exact hPbound