-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_clean_edge__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:24:42.42002+00:00
-- url     : https://prove2.me/submissions/264d166d-70b3-4bb9-bf17-23f846de3cf4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_clean_arc_augmented_drawing__p2m_a28e5ee4_bf60_4e7a_aa04_8ab47cd06895_a1
import Theorems.Thm_WilliamsonShmoys_strict_added_edge_finset__p2m_a28e5ee4_bf60_4e7a_aa04_8ab47cd06895_a1
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
    (huv : u < v) (hnonadj : ¬ K.Adj u v)
    (hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1))
    (hinj : Set.InjOn gamma (Set.Icc (0 : ℝ) 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (hvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (harcs : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → K.Adj x y →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s) :
    ∃ (L : SimpleGraph V) (hLdec : DecidableRel L.Adj),
      K.edgeFinset ⊂ L.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨L, hLdec, hLrel, hLdrawing⟩ :=
    WilliamsonShmoys.clean_arc_augmented_drawing__p2m_a28e5ee4_bf60_4e7a_aa04_8ab47cd06895_a1
      K p arc hp hdrawing hcross u v gamma huv hcont hinj hzero hone hvertices harcs
  letI := hLdec
  have hstrict :=
    WilliamsonShmoys.strict_added_edge_finset__p2m_a28e5ee4_bf60_4e7a_aa04_8ab47cd06895_a1
      K L u v huv hnonadj hLrel
  exact ⟨L, hLdec, hstrict, hLdrawing⟩