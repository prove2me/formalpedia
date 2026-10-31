-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_strict_supergraph_of_not_connected__p2m_bc735298_99fb_476e_aa8d_1e3af7f2e774_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:59:43.290448+00:00
-- url     : https://prove2.me/submissions/166cf83e-95bf-4a2d-877f-d22d487c2a3b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_strict_edge_count_of_new_adj__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1
import Theorems.Thm_WilliamsonShmoys_planar_bridge_augmentation__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKplanar : HasPlanarDrawingOn K)
    (hnot : ¬ K.Connected) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      K.edgeSet.ncard < L.edgeSet.ncard := by
  obtain ⟨L, hKL, hLplanar, u, v, hLuv, hKuv⟩ :=
    WilliamsonShmoys.planar_bridge_augmentation__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1
      K hKplanar hnot
  exact ⟨L, hKL, hLplanar,
    WilliamsonShmoys.strict_edge_count_of_new_adj__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1
      K L hKL u v hLuv hKuv⟩