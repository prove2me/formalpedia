-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_yields_euler_face_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:02:40.442452+00:00
-- url     : https://prove2.me/submissions/e1d0dd54-bef6-4433-90ed-50e84d3be304
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_component_count
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_components_exact

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hm : 2 ≤ L.edgeSet.ncard) :
    ∃ (f c : ℕ),
      Fintype.card V + f = L.edgeSet.ncard + c + 1 ∧
      1 ≤ c ∧
      3 * f ≤ 2 * L.edgeSet.ncard := by
  obtain ⟨f, heuler, hc⟩ :=
    WilliamsonShmoys.planar_drawing_euler_component_count L hV hL
  have hbound :=
    WilliamsonShmoys.planar_drawing_edge_bound_components_exact L hV hL hm
  refine ⟨f, Nat.card L.ConnectedComponent, heuler, hc, ?_⟩
  omega