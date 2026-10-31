-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:16:36.396839+00:00
-- url     : https://prove2.me/submissions/59ac8ce6-6f0d-4420-9c02-787d3b2a3b18

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_upper_bound__p2m_c23ffc9b_3ccd_4354_ad9d_982ada7aecad_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_c23ffc9b_3ccd_4354_ad9d_982ada7aecad_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, H ≤ L → HasPlanarDrawingOn L → L = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.maximal_planar_drawing_edge_count_upper_bound__p2m_c23ffc9b_3ccd_4354_ad9d_982ada7aecad_a1 H hH hV
  have hLower := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_c23ffc9b_3ccd_4354_ad9d_982ada7aecad_a1 H hH hV hMax
  omega