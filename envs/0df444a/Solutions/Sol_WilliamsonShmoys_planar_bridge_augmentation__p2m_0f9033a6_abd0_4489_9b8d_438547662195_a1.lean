-- Prove2me | solution 1 for WilliamsonShmoys.planar_bridge_augmentation__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:14:50.413627+00:00
-- url     : https://prove2.me/submissions/f34ef73e-e1a3-4dde-82e4-db686fc94b15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_has_unreachable_pair__p2m_9ff15d30_8739_4d4c_ada8_35f6650f3988_a1
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_across_unreachable_pair__p2m_9ff15d30_8739_4d4c_ada8_35f6650f3988_a1
open WilliamsonShmoys
set_option autoImplicit false

/-- Separate the components of a finite planar drawing and insert a bridge between two of them. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKplanar : HasPlanarDrawingOn K) (hnot : ¬ K.Connected) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ∃ u v : V, L.Adj u v ∧ ¬ K.Adj u v := by
  obtain ⟨u, v, hsep⟩ := WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_9ff15d30_8739_4d4c_ada8_35f6650f3988_a1 K hnot
  obtain ⟨L, hKL, hLplanar, huv, hnotuv⟩ := WilliamsonShmoys.planar_add_edge_across_unreachable_pair__p2m_9ff15d30_8739_4d4c_ada8_35f6650f3988_a1 K hKplanar hsep
  exact ⟨L, hKL, hLplanar, u, v, huv, hnotuv⟩