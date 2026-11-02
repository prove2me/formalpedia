-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_one_edge_augmentation__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:09.966364+00:00
-- url     : https://prove2.me/submissions/7e0d3f67-7563-4538-b0e0-9917e76bfb11
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_distinct_components_endpoints__p2m_68fcfb6b_9fe7_4d9c_85f0_a7b7f89a4ef9_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_geometry__p2m_68fcfb6b_9fe7_4d9c_85f0_a7b7f89a4ef9_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hnc : ¬ K.Connected) :
    ∃ a b : V, ∃ H : SimpleGraph V,
      ¬ K.Adj a b ∧ ¬ K.Reachable a b ∧
      (∀ u v, H.Adj u v ↔
        K.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨a, b, hab, hnotReachable⟩ :=
    WilliamsonShmoys.planar_drawing_distinct_components_endpoints__p2m_68fcfb6b_9fe7_4d9c_85f0_a7b7f89a4ef9_a2 K hnc
  obtain ⟨H, hAdj, hDrawing⟩ :=
    WilliamsonShmoys.planar_drawing_add_bridge_geometry__p2m_68fcfb6b_9fe7_4d9c_85f0_a7b7f89a4ef9_a2 K hK a b hab hnotReachable
  exact ⟨a, b, H, hab, hnotReachable, hAdj, hDrawing⟩