-- Prove2me | solution 1 for WilliamsonShmoys.planar_bridge_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:55:00.271565+00:00
-- url     : https://prove2.me/submissions/47e756d2-5b62-43a8-8ad6-be5e4087dec6

import Theorems.Thm_WilliamsonShmoys_planar_bridge_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (hnot : ¬ G.Reachable u v) :
    ∃ A B : Set V,
      (∀ x, x ∈ A ∨ x ∈ B) ∧
      Disjoint A B ∧
      u ∈ A ∧
      v ∈ B ∧
      (∀ x y, G.Adj x y → (x ∈ A ↔ y ∈ A)) :=
  WilliamsonShmoys.planar_bridge_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3 G u v hnot