-- Prove2me | solution 1 for WilliamsonShmoys.clean_arc_augmented_drawing__p2m_a28e5ee4_bf60_4e7a_aa04_8ab47cd06895_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:20:20.833039+00:00
-- url     : https://prove2.me/submissions/93bfebed-23b8-4ac9-8bd6-8031e76702c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_clean_arc_drawing_data__p2m_50ad6ee9_9926_4b70_a189_fa4f2cd3e119_a1
import Mathlib

set_option autoImplicit false

open Set

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
      WilliamsonShmoys.HasPlanarDrawingOn L := by
  simpa [WilliamsonShmoys.HasPlanarDrawingOn] using
    (WilliamsonShmoys.clean_arc_drawing_data__p2m_50ad6ee9_9926_4b70_a189_fa4f2cd3e119_a1
      K p arc hp hdrawing hcross u v gamma huv hcont hinj hzero hone hvertices harcs)