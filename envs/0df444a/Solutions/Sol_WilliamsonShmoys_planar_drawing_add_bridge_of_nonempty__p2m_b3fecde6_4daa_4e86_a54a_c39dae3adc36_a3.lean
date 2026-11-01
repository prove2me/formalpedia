-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_bridge_of_nonempty__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:16:33.625279+00:00
-- url     : https://prove2.me/submissions/a961d318-2110-4a36-b8e6-7604e800090f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_has_nonreachable_pair__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_fixed_bridge__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 2 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v, ¬ G.Reachable u v ∧ K.Adj u v := by
  obtain ⟨u, v, huv⟩ := WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1 G hcard hDisconnected
  obtain ⟨K, hsub, hK, hadj⟩ := WilliamsonShmoys.planar_drawing_add_fixed_bridge__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1 G hG huv
  exact ⟨K, hsub, hK, u, v, huv, hadj⟩