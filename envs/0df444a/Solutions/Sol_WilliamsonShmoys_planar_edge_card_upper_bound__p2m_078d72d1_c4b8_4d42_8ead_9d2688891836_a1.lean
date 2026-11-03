-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_card_upper_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:12:24.920874+00:00
-- url     : https://prove2.me/submissions/116ab084-784f-40c8-8354-350d6863fe44

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_card_upper_bound__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) [DecidableRel K.Adj]
    (hcard : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨L, hKL, hLconn, hLdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1
      K hcard hK
  have hL :=
    WilliamsonShmoys.connected_planar_edge_card_upper_bound__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1
      L hcard hLconn hLdraw
  exact (Finset.card_le_card (SimpleGraph.edgeFinset_mono hKL)).trans hL