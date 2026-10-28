-- Prove2me | solution 1 for WilliamsonShmoys.extend_of_safe_bridge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:48:34.717271+00:00
-- url     : https://prove2.me/submissions/e0e3ec1e-249a-41bc-904c-910b4e554a80
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_HasSafeBridge
import Theorems.Thm_WilliamsonShmoys_safe_bridge_graph_extension
import Theorems.Thm_WilliamsonShmoys_safe_bridge_drawing_extension

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
    (hBridge : HasSafeBridge G p arc) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v) ∧
      ∃ arc' : V → V → ℝ → ℝ × ℝ,
        (∀ u v, u < v → G.Adj u v → arc' u v = arc u v) ∧
        (∀ u v, u < v → H.Adj u v →
          ContinuousOn (arc' u v) (Set.Icc 0 1) ∧
          Set.InjOn (arc' u v) (Set.Icc 0 1) ∧
          arc' u v 0 = p u ∧
          arc' u v 1 = p v ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc' u v t ≠ p w) ∧
        (∀ u v x y, u < v → x < y → H.Adj u v → H.Adj x y →
          (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
            arc' u v t = arc' x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  obtain ⟨H, hsub, hedge, hnew⟩ :=
    WilliamsonShmoys.safe_bridge_graph_extension G p arc hBridge
  obtain ⟨arc', hold, hdraw, hcross⟩ :=
    WilliamsonShmoys.safe_bridge_drawing_extension G H p arc hp
      hEdgeDrawing hNoCrossing hBridge hsub hedge hnew
  exact ⟨H, hsub, hedge, hnew, arc', hold, hdraw, hcross⟩
