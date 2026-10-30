-- Prove2me | solution 1 for WilliamsonShmoys.addable_bridge_gives_strict_planar_supergraph__p2m_6953b2d1_377a_4f12_a204_4d1226429a63_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:00:41.26634+00:00
-- url     : https://prove2.me/submissions/cc7eea4d-0fbc-4626-bf01-1514c5b75d27

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_bridge_augmented_graph_has_planar_drawing__p2m_6d41a7cc_0330_45c8_a22c_836a8a445d01_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdges : ∀ a b, a < b → H.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hCross : ∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
      (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc a b t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (c : ℝ → ℝ × ℝ)
    (huv : u < v)
    (hnotadj : ¬ H.Adj u v)
    (hccont : ContinuousOn c (Set.Icc 0 1))
    (hcinj : Set.InjOn c (Set.Icc 0 1))
    (hc0 : c 0 = p u)
    (hc1 : c 1 = p v)
    (hcvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w)
    (hccross : ∀ x y, x < y → H.Adj x y → (u, v) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        c t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ H := by
  let M := H ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)
  refine ⟨M, ?_, ?_, ?_⟩
  · intro a b hab
    rw [SimpleGraph.sup_adj]
    exact Or.inl hab
  · exact bridge_augmented_graph_has_planar_drawing__p2m_6d41a7cc_0330_45c8_a22c_836a8a445d01_a1
      H p arc hp hEdges hCross u v c huv hccont hcinj hc0 hc1 hcvertices hccross
  · intro heq
    have hnew : M.Adj u v := by
      rw [SimpleGraph.sup_adj]
      right
      rw [SimpleGraph.fromRel_adj]
      exact ⟨huv.ne, Or.inl ⟨rfl, rfl⟩⟩
    exact hnotadj (heq ▸ hnew)
