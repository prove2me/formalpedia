-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:04:52.2018+00:00
-- url     : https://prove2.me/submissions/dd2b932a-4a62-48bd-a44d-39583f1974e2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card <= 3 * Fintype.card V - 6) := by
  classical
  have hBound : K.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_drawingOn_edge_bound K hK hV
  exact WilliamsonShmoys.edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1
    K (Classical.decRel K.Adj) hBound
