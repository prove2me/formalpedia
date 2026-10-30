-- Prove2me | solution 1 for WilliamsonShmoys.disconnectedDrawing_bridgeArc__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:14:30.161572+00:00
-- url     : https://prove2.me/submissions/3c6a396e-2bcc-4179-a543-54d15e233ca9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnectedDrawing_complementPath__p2m_7c92e097_26a8_4bba_9ade_61a98089220b_a1
import Theorems.Thm_WilliamsonShmoys_disconnectedDrawing_simpleArcOfComplementPath__p2m_7c92e097_26a8_4bba_9ade_61a98089220b_a1

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
    ∃ u v : V, ∃ gamma : ℝ → ℝ × ℝ,
      u < v ∧ ¬ G.Reachable u v ∧
      ContinuousOn gamma (Set.Icc 0 1) ∧ Set.InjOn gamma (Set.Icc 0 1) ∧
      gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
          gamma t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  obtain ⟨u, v, gamma, huv, hnot, hcont, hzero, hone, havoidV, havoidE⟩ :=
    WilliamsonShmoys.disconnectedDrawing_complementPath__p2m_7c92e097_26a8_4bba_9ade_61a98089220b_a1
      hV G p arc hp hEdge hCross hG_not_connected
  obtain ⟨delta, hδcont, hδinj, hδzero, hδone, hδavoidV, hδcross⟩ :=
    WilliamsonShmoys.disconnectedDrawing_simpleArcOfComplementPath__p2m_7c92e097_26a8_4bba_9ade_61a98089220b_a1
      G p arc hp hEdge u v huv hnot gamma hcont hzero hone havoidV havoidE
  exact ⟨u, v, delta, huv, hnot, hδcont, hδinj, hδzero, hδone, hδavoidV, hδcross⟩