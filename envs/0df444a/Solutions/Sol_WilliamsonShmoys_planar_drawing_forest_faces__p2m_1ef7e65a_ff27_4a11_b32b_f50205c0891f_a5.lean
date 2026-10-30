-- Prove2me | solution 1 for WilliamsonShmoys_planar_drawing_forest_faces__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:00:17.212111+00:00
-- url     : https://prove2.me/submissions/47ed7d7b-7a44-44be-997e-3b4680b3b94a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_b41a74fa_21d0_4a74_8cba_62a4d9ab4259_a1
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Tactic

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
    (H : SimpleGraph V)
    (hsub : ∀ u v, H.Adj u v → G.Adj u v)
    (hacyclic : H.IsAcyclic)
    (hspan : ∀ u v, G.Reachable u v → H.Reachable u v)
    (hcard : H.edgeSet.ncard + Nat.card G.ConnectedComponent = Fintype.card V) :
    Nat.card (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc) + H.edgeSet.ncard =
      G.edgeSet.ncard + 1 := by
  have heuler := WilliamsonShmoys_planar_drawing_euler_formula__p2m_b41a74fa_21d0_4a74_8cba_62a4d9ab4259_a1
    G p arc hp ha hi
  omega