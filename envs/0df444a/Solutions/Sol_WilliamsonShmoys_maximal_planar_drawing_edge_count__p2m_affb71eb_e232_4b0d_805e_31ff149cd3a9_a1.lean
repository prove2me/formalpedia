-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_affb71eb_e232_4b0d_805e_31ff149cd3a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:29:19.893283+00:00
-- url     : https://prove2.me/submissions/d206bdbd-e15b-4dfc-8701-12ddfdd42be3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1 L hcard hL
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1 L hcard hL hmax
  omega