-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_disconnected_path_augmentation__p2m_100679c8_dd25_4620_924f_9d4949429e29_a3__p2m_100679c8_dd25_4620_924f_9d4949429e29_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:51.880206+00:00
-- url     : https://prove2.me/submissions/fd4f20c0-0ce8-4bac-901b-202da7deec35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnectedDrawing_bridgeArc__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2
import Theorems.Thm_WilliamsonShmoys_disconnectedDrawing_packageBridge__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V) (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdge : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hCross : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hG_not_connected : ¬ G.Connected) :
    ∃ H : SimpleGraph V, ∃ q : V → V → ℝ → ℝ × ℝ, ∃ u v,
      G ≤ H ∧ u < v ∧ ¬ G.Reachable u v ∧ H.Adj u v ∧ ¬ G.Adj u v ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (q x y) (Set.Icc 0 1) ∧
        Set.InjOn (q x y) (Set.Icc 0 1) ∧
        q x y 0 = p x ∧ q x y 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, q x y t ≠ p w) ∧
        (∀ a b, a < b → H.Adj a b → (x, y) ≠ (a, b) →
          ∀ t ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1,
            q x y t = q a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc 0 1, q x y t = arc x y t) := by
  obtain ⟨u, v, gamma, huv, hreach, hcont, hinj, hzero, hone, hvertex, hcrossGamma⟩ :=
    WilliamsonShmoys.disconnectedDrawing_bridgeArc__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2
      hV G p arc hp hEdge hCross hG_not_connected
  exact WilliamsonShmoys.disconnectedDrawing_packageBridge__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2
    hV G p arc hp hEdge hCross hG_not_connected u v gamma huv hreach hcont hinj hzero hone hvertex hcrossGamma