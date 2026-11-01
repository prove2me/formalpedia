-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_subgraph__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:17:39.83851+00:00
-- url     : https://prove2.me/submissions/be6546cc-2b67-4d08-bdee-b1c4feaed6b3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp_injective, h_edges, h_intersections⟩
  refine ⟨p, arc, hp_injective, ?_, ?_⟩
  · intro u v huv hG
    exact h_edges u v huv (hGH hG)
  · intro u v x y huv hxy hG hG' hne t ht s hs heq
    exact h_intersections u v x y huv hxy (hGH hG) (hGH hG') hne t ht s hs heq