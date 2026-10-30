-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_edge_maximal_planar
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:43:49.952394+00:00
-- url     : https://prove2.me/submissions/90c7cb85-1a9d-4e11-95e3-66a1a171a60b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hu := WilliamsonShmoys.planar_edge_count_upper_bound M hM hV
  have hl := WilliamsonShmoys.maximal_planar_edge_count_lower_bound M hM hV hmax
  omega