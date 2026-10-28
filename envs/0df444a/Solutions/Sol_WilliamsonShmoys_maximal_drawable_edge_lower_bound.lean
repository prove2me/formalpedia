-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:17:07.509984+00:00
-- url     : https://prove2.me/submissions/486951c4-dbff-4eff-b700-c9ccee063fb7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKdraw, hKcard⟩ :=
    WilliamsonShmoys.planar_drawable_supergraph_triangulation H hV hH
  have hKH : K ≤ H := hmax K hHK hKdraw
  have hEq : H = K := le_antisymm hHK hKH
  rw [hEq, hKcard]