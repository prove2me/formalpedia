-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_embedding_joining_arc__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:26:40.005583+00:00
-- url     : https://prove2.me/submissions/e0ac663a-da66-4b77-81f7-e1d6ab55a8ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_disconnected_ordered_unreachable__p2m_f5d9ac23_37a8_4813_be64_33098d8dbd1e_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_arc_for_unreachable_vertices__p2m_f5d9ac23_37a8_4813_be64_33098d8dbd1e_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hdrawing : ∀ u v, u < v → K.Adj u v →
      ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hcross : ∀ u v x y, u < v → x < y → K.Adj u v → K.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
        (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hdis : ¬ K.Connected) :
    ∃ (u v : V) (gamma : ℝ → ℝ × ℝ),
      u < v ∧ ¬ K.Adj u v ∧
      ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
      gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → K.Adj x y →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s) := by
  obtain ⟨u, v, huv, hnr⟩ :=
    WilliamsonShmoys.disconnected_ordered_unreachable__p2m_f5d9ac23_37a8_4813_be64_33098d8dbd1e_a2 K hdis
  obtain ⟨hne, gamma, hcont, hinj, hzero, hone, hvertices, hedges⟩ :=
    WilliamsonShmoys.planar_drawing_arc_for_unreachable_vertices__p2m_f5d9ac23_37a8_4813_be64_33098d8dbd1e_a2
      K p arc hp hdrawing hcross u v huv hnr
  exact ⟨u, v, gamma, huv, hne, hcont, hinj, hzero, hone, hvertices, hedges⟩