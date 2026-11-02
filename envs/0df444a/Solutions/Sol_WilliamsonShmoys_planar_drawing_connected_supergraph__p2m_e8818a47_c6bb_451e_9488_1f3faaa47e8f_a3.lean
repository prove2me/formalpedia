-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T00:31:47.506334+00:00
-- url     : https://prove2.me/submissions/51c59a70-028f-485e-8b45-51a62c6f5fd8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3
import Theorems.Thm_WilliamsonShmoys_subgraph_edgeFinset_card_mono__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      ∃ H : SimpleGraph V,
        HasPlanarDrawingOn H ∧ H.Connected ∧
          K.edgeFinset.card ≤
            (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
              H.edgeFinset.card)) := by
  classical
  obtain ⟨H, hKH, hConn, hDraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3
      K hcard hK
  refine ⟨H, hDraw, hConn, ?_⟩
  exact WilliamsonShmoys.subgraph_edgeFinset_card_mono__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
    K H hKH