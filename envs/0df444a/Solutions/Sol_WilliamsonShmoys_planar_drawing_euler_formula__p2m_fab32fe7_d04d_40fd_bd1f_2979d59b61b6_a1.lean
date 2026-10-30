-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_formula__p2m_fab32fe7_d04d_40fd_bd1f_2979d59b61b6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:57:16.1165+00:00
-- url     : https://prove2.me/submissions/baa0efe9-884d-4b75-8e1c-e83f82287461
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_spanning_forest__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5
import Theorems.Thm_WilliamsonShmoys_planar_drawing_forest_faces__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (ha : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hi : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    Nat.card (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc) + Fintype.card V =
      G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
  obtain ⟨H, hsub, hacyclic, hspan, hcard⟩ :=
    WilliamsonShmoys_planar_drawing_spanning_forest__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5 G
  have hfaces :=
    WilliamsonShmoys_planar_drawing_forest_faces__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5
      G p arc hp ha hi H hsub hacyclic hspan hcard
  omega