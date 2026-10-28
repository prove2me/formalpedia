-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_yields_euler_face_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:29:31.481507+00:00
-- url     : https://prove2.me/submissions/e03c1d78-bb3a-4e75-b0d3-2e3135e9f8cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_relation
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_bound

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
  obtain ⟨f, c, heuler, hc⟩ :=
    WilliamsonShmoys.planar_drawing_euler_relation L hV hL
  have hbound :=
    WilliamsonShmoys.planar_drawing_euler_face_bound L hV hL hm f c heuler
  exact ⟨f, c, heuler, hc, hbound⟩