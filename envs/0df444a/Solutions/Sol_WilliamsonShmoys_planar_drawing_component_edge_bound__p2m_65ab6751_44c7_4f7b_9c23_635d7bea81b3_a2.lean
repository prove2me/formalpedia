-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_component_edge_bound__p2m_65ab6751_44c7_4f7b_9c23_635d7bea81b3_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:39:04.72163+00:00
-- url     : https://prove2.me/submissions/f302cf48-8323-46cc-a9f4-0d3127821df8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler__p2m_78694808_3d0f_4e5c_944c_19b55c0ff3fe_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_degree_bound__p2m_78694808_3d0f_4e5c_944c_19b55c0ff3fe_a2
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

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
    G.edgeSet.ncard + 3 * Nat.card G.ConnectedComponent + 3 ≤
      3 * Fintype.card V := by
  let F := Nat.card
    (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
      G p arc)
  have hEuler :=
    WilliamsonShmoys.planar_drawing_euler__p2m_78694808_3d0f_4e5c_944c_19b55c0ff3fe_a2
      G p arc hp ha hi
  have hDegree :=
    WilliamsonShmoys.planar_drawing_face_degree_bound__p2m_78694808_3d0f_4e5c_944c_19b55c0ff3fe_a2
      G p arc hp ha hi hE
  change G.edgeSet.ncard + 3 * Nat.card G.ConnectedComponent + 3 ≤
    3 * Fintype.card V
  have hEuler' :
      Fintype.card V + F = G.edgeSet.ncard + 1 + Nat.card G.ConnectedComponent := by
    simpa [F] using hEuler
  have hDegree' : 3 * F ≤ 2 * G.edgeSet.ncard := by
    simpa [F] using hDegree
  omega