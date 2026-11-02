-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_bridge_setup_of_unreachable__p2m_6b761602_ec4e_4b71_82d8_bcea18a590f0_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:06:27.418919+00:00
-- url     : https://prove2.me/submissions/55b3e73e-c592-41c0-ab1a-df099089022a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_of_unreachable__p2m_f0a53f14_3d07_482d_8483_9c70fdc17ecd_a1
import Theorems.Thm_WilliamsonShmoys_extract_added_edge_as_bridge__p2m_f0a53f14_3d07_482d_8483_9c70fdc17ecd_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (u v : V) (hnot : ¬ H.Reachable u v) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
      (bridge : ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ a b, a < b → H.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧
        arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
        (a, b) ≠ (x, y) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc a b t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn bridge (Set.Icc (0 : ℝ) 1) ∧
      bridge 0 = p u ∧
      bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  exact WilliamsonShmoys.extract_added_edge_as_bridge__p2m_f0a53f14_3d07_482d_8483_9c70fdc17ecd_a1
    H hH u v hnot
    (WilliamsonShmoys.planar_drawing_add_edge_of_unreachable__p2m_f0a53f14_3d07_482d_8483_9c70fdc17ecd_a1
      H hH u v hnot)