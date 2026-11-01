-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_of_bridges__p2m_977ef0e9_2b10_4ce9_abb8_e8741d8c6875_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:59:54.240481+00:00
-- url     : https://prove2.me/submissions/8027017c-0d5c-4c8b-a24e-b130ba6378f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
import Theorems.Thm_WilliamsonShmoys_iterate_planar_bridge_extensions__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hbridge : ∀ (G : SimpleGraph V), (dG : DecidableRel G.Adj) →
      WilliamsonShmoys.HasPlanarDrawingOn G →
      ∀ u v, ¬ G.Reachable u v →
        ∃ H : SimpleGraph V,
          (∀ a b, H.Adj a b ↔
            G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
          WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  apply WilliamsonShmoys.iterate_planar_bridge_extensions__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
    K dK hK
  intro G dG hG u v hnot
  exact WilliamsonShmoys.planar_drawing_add_bridge__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
    G dG hG u v hnot