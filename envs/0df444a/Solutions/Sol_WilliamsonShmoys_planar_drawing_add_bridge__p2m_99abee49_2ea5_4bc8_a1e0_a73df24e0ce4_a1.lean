-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_bridge__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:31:20.2796+00:00
-- url     : https://prove2.me/submissions/fdcf6571-6bf9-40b0-a929-2a342298bcd6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_induce__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
import Theorems.Thm_WilliamsonShmoys_planar_bridge_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_across_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (hnot : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  classical
  obtain ⟨A, B, hcover, hdisjoint, hu, hv, hcross⟩ :=
    WilliamsonShmoys.planar_bridge_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
      G u v hnot
  have hA : WilliamsonShmoys.HasPlanarDrawingOn (G.induce A) :=
    WilliamsonShmoys.planar_drawing_induce__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
      G A hG
  have hB : WilliamsonShmoys.HasPlanarDrawingOn (G.induce B) :=
    WilliamsonShmoys.planar_drawing_induce__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
      G B hG
  exact WilliamsonShmoys.planar_drawing_add_bridge_across_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
    G A B u v hA hB hcover hdisjoint hcross hu hv