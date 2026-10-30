-- Prove2me | solution 1 for WilliamsonShmoys.bridge_curve_reverse__p2m_6ebb6941_3575_43d9_99fa_a3f3a344e2d8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:46.982772+00:00
-- url     : https://prove2.me/submissions/b45fe306-27c6-44b0-b535-0e5582219cc2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (x y : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hedge : ∀ u v, u < v → H.Adj u v →
      ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hadj : H.Adj y x) (hrev : y < x) :
    ∃ γ : ℝ → ℝ × ℝ,
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = p x ∧ γ 1 = p y ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t = arc y x (1 - t)) := by
  rcases hedge y x hrev hadj with ⟨hcont, hinj, h0, h1, havoid⟩
  let γ : ℝ → ℝ × ℝ := fun t => arc y x (1 - t)
  have hflip : ContinuousOn (fun t : ℝ => 1 - t) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.sub continuousOn_id
  have hmap : Set.MapsTo (fun t : ℝ => 1 - t)
      (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    constructor <;> simp only [Set.mem_Icc] at ht ⊢ <;> linarith
  have hintmap : Set.MapsTo (fun t : ℝ => 1 - t)
      (Set.Ioo (0 : ℝ) 1) (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    constructor <;> simp only [Set.mem_Ioo] at ht ⊢ <;> linarith
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ContinuousOn (fun t : ℝ => arc y x (1 - t)) (Set.Icc (0 : ℝ) 1)
    exact hcont.comp hflip hmap
  · intro a ha b hb hab
    change arc y x (1 - a) = arc y x (1 - b) at hab
    have hargs := hinj (hmap ha) (hmap hb) hab
    dsimp at hargs
    linarith
  · simp [γ, h1]
  · simp [γ, h0]
  · intro t ht w
    have ht' := hintmap ht
    simpa [γ] using havoid (1 - t) ht' w
  · intro t ht
    rfl