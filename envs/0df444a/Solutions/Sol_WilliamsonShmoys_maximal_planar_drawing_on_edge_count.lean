-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_on_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:11:22.83746+00:00
-- url     : https://prove2.me/submissions/159cce59-c179-443a-8335-ef4599dcbc64

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_supergraph_triangulation_count
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_supergraph_triangulation_count L hL hV
  have hEq : M = L := hMax M hLM hM
  subst M
  exact hCount