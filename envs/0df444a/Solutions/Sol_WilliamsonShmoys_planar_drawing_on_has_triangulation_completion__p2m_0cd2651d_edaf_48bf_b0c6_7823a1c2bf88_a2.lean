-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_has_triangulation_completion__p2m_0cd2651d_edaf_48bf_b0c6_7823a1c2bf88_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:13:07.173335+00:00
-- url     : https://prove2.me/submissions/bbe26ebb-19ec-439d-a1fe-b00037d3f6e7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_has_inclusion_maximal_completion__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_inclusion_maximal_edge_count__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    Exists fun U : SimpleGraph V =>
      T ≤ U ∧ HasPlanarDrawingOn U ∧
        3 * Fintype.card V - 6 = U.edgeSet.ncard := by
  obtain ⟨U, hTU, hU, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_on_has_inclusion_maximal_completion__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1
      T hT
  exact ⟨U, hTU, hU,
    WilliamsonShmoys.planar_drawing_on_inclusion_maximal_edge_count__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1
      U hV hU hmax⟩