-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension_edge_bound_count_79011c86fe2a4d17
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:42:34.032144+00:00
-- url     : https://prove2.me/submissions/5e4f3728-1488-46e1-9e60-e8d94db942fb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_79011c86fe2a4d17
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_79011c86fe2a4d17

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N <= P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P <= N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hu :=
    WilliamsonShmoys.planar_drawing_edge_bound_79011c86fe2a4d17 N hV hN
  have hl :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_79011c86fe2a4d17
      N hV hN hmax
  omega