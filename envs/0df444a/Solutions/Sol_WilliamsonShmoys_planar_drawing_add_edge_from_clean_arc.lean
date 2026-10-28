-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_from_clean_arc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:34:08.772895+00:00
-- url     : https://prove2.me/submissions/d8825fa4-2cc9-4675-ad17-40be1b578dff

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_sup_from_clean_arc
import Theorems.Thm_WilliamsonShmoys_add_edge_strict_of_unreachable

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    {u v : V}
    (huv : u < v)
    (hUnreachable : ¬ G.Reachable u v)
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
    ∃ H : SimpleGraph V,
      G < H ∧ H.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  let K := SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)
  let H := G ⊔ K
  have hK : K.Adj u v := by
    rw [SimpleGraph.fromRel_adj]
    exact ⟨ne_of_lt huv, Or.inl ⟨rfl, rfl⟩⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · exact WilliamsonShmoys.add_edge_strict_of_unreachable G huv hUnreachable
  · exact (SimpleGraph.sup_adj G K u v).2 (Or.inr hK)
  · exact WilliamsonShmoys.planar_drawingOn_sup_from_clean_arc
      G huv p arc γ hp hEdges hCross hγContinuous hγInjective
      hγStart hγEnd hγAvoid hγCross
