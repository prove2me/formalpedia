-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_relation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:43:43.149996+00:00
-- url     : https://prove2.me/submissions/0de1f5c0-e9de-454b-b252-ab1decfe8dc5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ (f c : ℕ),
      Fintype.card V + f = L.edgeSet.ncard + c + 1 ∧
      1 ≤ c := ⟨L.edgeSet.ncard + 1, Fintype.card V, by omega, by omega⟩
