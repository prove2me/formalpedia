-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_from_drawing_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:12:42.536925+00:00
-- url     : https://prove2.me/submissions/7829ff02-5c36-469e-b272-71f068df5cce

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_from_embedding

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M)
    (hmax : ∀ K : SimpleGraph V, M.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K → K = M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_drawing_edge_bound_from_embedding M hV hMdraw