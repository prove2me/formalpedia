-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension__p2m_2260a117_6439_491e_b3cc_351c9a5eff37_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:15:12.822257+00:00
-- url     : https://prove2.me/submissions/4da581f7-0652-46ec-b088-0804729ce5f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_nonreachable_pair__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_admits_component_bridge_strict__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K ≠ G := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.disconnected_planar_drawing_has_nonreachable_pair__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a1
      G hcard hDisconnected
  obtain ⟨K, hGK, hKuv, hK, hKne⟩ :=
    WilliamsonShmoys.planar_drawing_admits_component_bridge_strict__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a2
      G hG huv
  exact ⟨K, hGK, hK, hKne⟩