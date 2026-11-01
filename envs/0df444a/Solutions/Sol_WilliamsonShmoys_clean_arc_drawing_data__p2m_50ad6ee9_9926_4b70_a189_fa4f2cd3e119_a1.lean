-- Prove2me | solution 1 for WilliamsonShmoys.clean_arc_drawing_data__p2m_50ad6ee9_9926_4b70_a189_fa4f2cd3e119_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:51:14.201887+00:00
-- url     : https://prove2.me/submissions/f2f0b783-9d69-410d-ade1-ddb652e789d7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_clean_arc_drawing_geometry__p2m_a073dd38_4e30_4f95_9bdc_3dc54f59a882_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hdrawing : ∀ x y, x < y → K.Adj x y →
      ContinuousOn (arc x y) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc x y) (Set.Icc (0 : ℝ) 1) ∧
      arc x y 0 = p x ∧ arc x y 1 = p y ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)
    (hcross : ∀ x y a b, x < y → a < b → K.Adj x y → K.Adj a b →
      (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, arc x y t = arc a b s →
        (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (gamma : ℝ → ℝ × ℝ)
    (huv : u < v)
    (hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1))
    (hinj : Set.InjOn gamma (Set.Icc (0 : ℝ) 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (hvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (harcs : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → K.Adj x y →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s) :
    ∃ (L : SimpleGraph V) (hLdec : DecidableRel L.Adj),
      (∀ a b, L.Adj a b ↔
        K.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      ∃ (q : V → ℝ × ℝ) (β : V → V → ℝ → ℝ × ℝ),
        Function.Injective q ∧
        (∀ x y, x < y → L.Adj x y →
          ContinuousOn (β x y) (Set.Icc (0 : ℝ) 1) ∧
          Set.InjOn (β x y) (Set.Icc (0 : ℝ) 1) ∧
          β x y 0 = q x ∧ β x y 1 = q y ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, β x y t ≠ q w) ∧
        (∀ x y a b, x < y → a < b → L.Adj x y → L.Adj a b →
          (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ s ∈ Set.Icc (0 : ℝ) 1, β x y t = β a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  classical
  let L : SimpleGraph V := {
    Adj := fun a b => K.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))
    symm := ⟨by
      intro a b hab
      rcases hab with hK | h
      · exact Or.inl (K.symm.symm a b hK)
      · rcases h with huv' | hvu'
        · exact Or.inr (Or.inr ⟨huv'.2, huv'.1⟩)
        · exact Or.inr (Or.inl ⟨hvu'.2, hvu'.1⟩)
    ⟩
    loopless := ⟨by
      intro a ha
      rcases ha with hK | h
      · exact K.loopless.irrefl a hK
      · rcases h with huv' | hvu'
        · exact (ne_of_lt huv) (huv'.1.symm.trans huv'.2)
        · exact (ne_of_lt huv).symm (hvu'.1.symm.trans hvu'.2)
    ⟩
  }
  have hL : ∀ a b, L.Adj a b ↔
      K.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by
    intro a b
    rfl
  let hLdec : DecidableRel L.Adj := Classical.decRel _
  refine ⟨L, hLdec, hL, ?_⟩
  exact WilliamsonShmoys.clean_arc_drawing_geometry__p2m_a073dd38_4e30_4f95_9bdc_3dc54f59a882_a2
    K p arc hp hdrawing hcross u v gamma huv hcont hinj hzero hone hvertices harcs L hL