-- Prove2me | solution 1 for WilliamsonShmoys.exists_safe_bridge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:54:46.826006+00:00
-- url     : https://prove2.me/submissions/91b626c7-4ea0-47ca-87b0-78d7c8534b4b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_HasSafeBridge
import Theorems.Thm_WilliamsonShmoys_exists_ordered_unreachable_vertices
import Theorems.Thm_WilliamsonShmoys_safe_bridge_between_unreachable_vertices

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdgeDrawing : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧
      arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hNoCrossing : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hCard : 3 ≤ Fintype.card V) (hGdisc : ¬ G.Connected) :
    WilliamsonShmoys.HasSafeBridge G p arc := by
  obtain ⟨u, v, huv, hUnreachable⟩ :=
    WilliamsonShmoys.exists_ordered_unreachable_vertices G hCard hGdisc
  obtain ⟨bridge, hCont, hInj, hStart, hFinish, hAvoid, hMeet⟩ :=
    WilliamsonShmoys.safe_bridge_between_unreachable_vertices
      G p arc hp hEdgeDrawing hNoCrossing u v huv hUnreachable
  exact ⟨u, v, huv, hUnreachable, bridge, hCont, hInj, hStart, hFinish, hAvoid, hMeet⟩