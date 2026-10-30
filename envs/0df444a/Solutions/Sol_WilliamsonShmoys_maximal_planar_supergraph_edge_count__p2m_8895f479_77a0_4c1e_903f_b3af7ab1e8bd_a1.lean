-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:59:55.08845+00:00
-- url     : https://prove2.me/submissions/7aa493ad-18bf-4fb3-9b52-9d07a5c251cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet = L.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_drawing_edge_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
    K hK hV
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
    K hK hV hmax
  omega