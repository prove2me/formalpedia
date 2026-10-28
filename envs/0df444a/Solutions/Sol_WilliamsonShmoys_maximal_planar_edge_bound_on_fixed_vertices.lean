-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_on_fixed_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:45:00.98085+00:00
-- url     : https://prove2.me/submissions/5ebdaff6-f3a1-420f-ba61-5b106cced992
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_on_fixed_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ X : SimpleGraph V,
      G ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X ≤ G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨X, hGX, hXplanar, htri⟩ :=
    WilliamsonShmoys.maximal_planar_completion_on_fixed_vertices G hV hG
  have hXG : X ≤ G := hmax X hGX hXplanar
  have hEq : G = X := le_antisymm hGX hXG
  rw [hEq]
  omega