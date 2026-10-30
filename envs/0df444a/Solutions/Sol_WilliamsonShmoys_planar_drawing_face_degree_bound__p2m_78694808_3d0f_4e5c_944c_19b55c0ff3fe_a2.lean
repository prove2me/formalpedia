-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_degree_bound__p2m_78694808_3d0f_4e5c_944c_19b55c0ff3fe_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:43:16.60531+00:00
-- url     : https://prove2.me/submissions/8c2f5da9-b776-4d90-8aa6-6c57617f0bd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_fab32fe7_d04d_40fd_bd1f_2979d59b61b6_a1
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_density__p2m_fab32fe7_d04d_40fd_bd1f_2979d59b61b6_a1

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
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hE : 2 ≤ G.edgeSet.ncard) :
    3 * Nat.card (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc) ≤
      2 * G.edgeSet.ncard := by
  have hEuler := WilliamsonShmoys.planar_drawing_euler_formula__p2m_fab32fe7_d04d_40fd_bd1f_2979d59b61b6_a1
    G p arc hp ha hi
  have hDensity := WilliamsonShmoys.planar_simple_edge_density__p2m_fab32fe7_d04d_40fd_bd1f_2979d59b61b6_a1
    G p arc hp ha hi hE
  nlinarith [hEuler, hDensity]