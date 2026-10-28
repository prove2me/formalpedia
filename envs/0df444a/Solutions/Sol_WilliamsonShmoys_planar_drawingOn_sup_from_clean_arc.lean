-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_sup_from_clean_arc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:56:22.836853+00:00
-- url     : https://prove2.me/submissions/c36c2051-a97b-4987-9019-994ccbd4f4d7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_extended_drawing_data_from_clean_arc

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    {u v : V}
    (huv : u < v)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (γ : ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdges : ∀ x y, x < y → G.Adj x y →
      ContinuousOn (arc x y) (Set.Icc 0 1) ∧
      Set.InjOn (arc x y) (Set.Icc 0 1) ∧
      arc x y 0 = p x ∧ arc x y 1 = p y ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)
    (hCross : ∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
      (x, y) ≠ (a, b) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc x y t = arc a b s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hγContinuous : ContinuousOn γ (Set.Icc 0 1))
    (hγInjective : Set.InjOn γ (Set.Icc 0 1))
    (hγStart : γ 0 = p u)
    (hγEnd : γ 1 = p v)
    (hγAvoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (hγCross : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        γ t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    WilliamsonShmoys.HasPlanarDrawingOn
      (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)) := by
  rcases WilliamsonShmoys.extended_drawing_data_from_clean_arc
      G huv p arc γ hp hEdges hCross hγContinuous hγInjective
      hγStart hγEnd hγAvoid hγCross with ⟨arcNew, hEdgesNew, hCrossNew⟩
  exact ⟨p, arcNew, hp, hEdgesNew, hCrossNew⟩