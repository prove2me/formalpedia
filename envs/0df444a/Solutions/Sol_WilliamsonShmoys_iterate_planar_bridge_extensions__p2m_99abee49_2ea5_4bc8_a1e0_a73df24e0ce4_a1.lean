-- Prove2me | solution 1 for WilliamsonShmoys.iterate_planar_bridge_extensions__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:03:55.446565+00:00
-- url     : https://prove2.me/submissions/fea23123-96f6-40c1-9de6-1caaca2f575a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_extension_of_pairwise_bridge_closure__p2m_596e37ff_bf61_48b7_90c3_a4814329de9c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hstep : ∀ (G : SimpleGraph V), (dG : DecidableRel G.Adj) →
      WilliamsonShmoys.HasPlanarDrawingOn G →
      ∀ u v, ¬ G.Reachable u v →
        ∃ H : SimpleGraph V,
          (∀ a b, H.Adj a b ↔
            G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
          WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  classical
  exact WilliamsonShmoys.connected_extension_of_pairwise_bridge_closure__p2m_596e37ff_bf61_48b7_90c3_a4814329de9c_a1
    WilliamsonShmoys.HasPlanarDrawingOn K dK hK hstep