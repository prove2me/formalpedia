-- Prove2me | solution 1 for WilliamsonShmoys.planar_sparse_graph_has_drawable_strict_extension__p2m_19289cd0_8bc0_4354_9e78_5126f5795da0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:28:28.774424+00:00
-- url     : https://prove2.me/submissions/c742c66a-66aa-4712-9563-ebb943571b1b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_sparse_graph_has_drawable_strict_extension_dichotomy__p2m_5bb20037_ccd1_423f_b2f4_e98cccbfec38_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hSparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ M ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by
  rcases WilliamsonShmoys.planar_sparse_graph_has_drawable_strict_extension_dichotomy__p2m_5bb20037_ccd1_423f_b2f4_e98cccbfec38_a1
      L hL hCard with hExtend | hMaximal
  · exact hExtend
  · omega