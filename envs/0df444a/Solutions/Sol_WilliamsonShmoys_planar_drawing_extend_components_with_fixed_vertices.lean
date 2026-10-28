-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extend_components_with_fixed_vertices
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:53:47.131835+00:00
-- url     : https://prove2.me/submissions/a00e9977-89e1-47bc-94bc-2eef1a1ae1cd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
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
      (hGdisc : ¬ G.Connected),
      ∃ H : SimpleGraph V,
        G.edgeSet ⊆ H.edgeSet ∧
        (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
        (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v) ∧
        ∃ arc' : V → V → ℝ → ℝ × ℝ,
          (∀ u v, u < v → H.Adj u v →
            ContinuousOn (arc' u v) (Set.Icc 0 1) ∧
            Set.InjOn (arc' u v) (Set.Icc 0 1) ∧
            arc' u v 0 = p u ∧
            arc' u v 1 = p v ∧
            ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc' u v t ≠ p w) ∧
          (∀ u v x y, u < v → x < y → H.Adj u v → H.Adj x y →
            (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
              arc' u v t = arc' x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) := by
  intro h
  let p : Empty → ℝ × ℝ := fun x => nomatch x
  let arc : Empty → Empty → ℝ → ℝ × ℝ := fun u _ _ => nomatch u
  have hp : Function.Injective p := by
    intro x y hxy
    cases x
  have hEdgeDrawing : ∀ u v, u < v → (⊥ : SimpleGraph Empty).Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w := by
    intro u v huv hadj
    cases u
  have hNoCrossing : ∀ u v x y, u < v → x < y →
      (⊥ : SimpleGraph Empty).Adj u v → (⊥ : SimpleGraph Empty).Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
    intro u v x y huv hxy hadj hadj' hpairs t ht s hs heq
    cases u
  have hGdisc : ¬ (⊥ : SimpleGraph Empty).Connected := by
    simp [SimpleGraph.connected_bot_iff]
  obtain ⟨H, _, _, ⟨u, v, _, _⟩, _⟩ :=
    h (V := Empty) (G := ⊥) p arc hp hEdgeDrawing hNoCrossing hGdisc
  cases u