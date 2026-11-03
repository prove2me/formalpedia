-- Prove2me | solution 1 for WilliamsonShmoys.lower_half_plane_bridge_for_planar_drawing__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:21:22.240952+00:00
-- url     : https://prove2.me/submissions/102b27ad-371b-4c22-bc84-5762e439c4ea

import Theorems.Thm_WilliamsonShmoys_lower_half_plane_bridge_for_planar_drawing__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hdraw : Function.Injective p ∧
      (∀ a b, a < b → G.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b c d, a < b → c < d → G.Adj a b → G.Adj c d →
        (a, b) ≠ (c, d) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc a b t = arc c d s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    {u v : V}
    (hpu : (p u).2 = 0) (hpv : (p v).2 = 0)
    (hx : (p u).1 < (p v).1)
    (hvertices : ∀ w, w ≠ u → w ≠ v → 0 < (p w).2)
    (harcs : ∀ a b, a < b → G.Adj a b →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < (arc a b t).2) :
    ∃ gamma : ℝ → ℝ × ℝ,
      ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
      gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ a b, a < b → G.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          gamma t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :=
  WilliamsonShmoys.lower_half_plane_bridge_for_planar_drawing__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4 G p arc hdraw hpu hpv hx hvertices harcs