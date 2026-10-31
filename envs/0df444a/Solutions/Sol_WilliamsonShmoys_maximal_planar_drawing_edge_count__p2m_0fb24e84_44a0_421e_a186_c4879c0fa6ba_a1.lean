-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:17:30.075312+00:00
-- url     : https://prove2.me/submissions/3e3a133b-221c-4c97-931c-325a733add54

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1

set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1
    L hV hDraw
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1
    L hV hDraw hmax
  omega