-- Prove2me | solution 1 for WilliamsonShmoys.disconnectedDrawing_packageBridge__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:58.738909+00:00
-- url     : https://prove2.me/submissions/f7d4178a-1d83-4370-9873-0f665172d024

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_bridgeAddDisconnectedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3
import Theorems.Thm_WilliamsonShmoys_bridgeArcExtensionOnAddedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3

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
    (hG_not_connected : ¬ G.Connected)
    (u v : V) (gamma : ℝ → ℝ × ℝ)
    (huv : u < v) (hreach : ¬ G.Reachable u v)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hinj : Set.InjOn gamma (Set.Icc 0 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (hvertex : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (hcrossGamma : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1,
        gamma t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    ∃ H : SimpleGraph V, ∃ q : V → V → ℝ → ℝ × ℝ, ∃ a b,
      G ≤ H ∧ a < b ∧ ¬ G.Reachable a b ∧ H.Adj a b ∧ ¬ G.Adj a b ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (q x y) (Set.Icc 0 1) ∧
        Set.InjOn (q x y) (Set.Icc 0 1) ∧
        q x y 0 = p x ∧ q x y 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, q x y t ≠ p w) ∧
        (∀ c d, c < d → H.Adj c d → (x, y) ≠ (c, d) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
            q x y t = q c d s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      (∀ x y, x < y → G.Adj x y → ∀ t ∈ Set.Icc 0 1, q x y t = arc x y t) := by
  obtain ⟨H, hle, hAdj, hnew, hnot⟩ :=
    WilliamsonShmoys.bridgeAddDisconnectedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3
      G u v huv hreach
  obtain ⟨q, hq, hpres⟩ :=
    WilliamsonShmoys.bridgeArcExtensionOnAddedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3
      G p arc hp hEdge hCross u v gamma huv hreach hcont hinj hzero hone hvertex
      hcrossGamma H hAdj
  exact ⟨H, q, u, v, hle, huv, hreach, hnew, hnot, hq, hpres⟩