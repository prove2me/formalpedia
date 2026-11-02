-- Prove2me | solution 1 for WilliamsonShmoys.planar_bridge_curve_for_disconnected_vertices__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:28:18.122657+00:00
-- url     : https://prove2.me/submissions/135c79cf-2e49-4117-9d26-03c739f06dec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_with_two_roots_on_common_exterior_line__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4
import Theorems.Thm_WilliamsonShmoys_lower_half_plane_bridge_for_planar_drawing__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (hnot : ¬ G.Reachable u v) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
      (gamma : ℝ → ℝ × ℝ),
      (Function.Injective p ∧
        (∀ a b, a < b → G.Adj a b →
          ContinuousOn (arc a b) (Set.Icc 0 1) ∧
          Set.InjOn (arc a b) (Set.Icc 0 1) ∧
          arc a b 0 = p a ∧ arc a b 1 = p b ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
        (∀ a b c d, a < b → c < d → G.Adj a b → G.Adj c d →
          (a, b) ≠ (c, d) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            arc a b t = arc c d s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      (ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
        Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
        gamma 0 = p u ∧ gamma 1 = p v ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
        (∀ a b, a < b → G.Adj a b →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            gamma t = arc a b s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) := by
  obtain ⟨p, arc, hdraw, hpu, hpv, hx, hvertices, harcs⟩ :=
    WilliamsonShmoys.planar_drawing_with_two_roots_on_common_exterior_line__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4
      G hG hnot
  obtain ⟨gamma, hgamma⟩ :=
    WilliamsonShmoys.lower_half_plane_bridge_for_planar_drawing__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4
      G p arc hdraw hpu hpv hx hvertices harcs
  exact ⟨p, arc, gamma, hdraw, hgamma⟩