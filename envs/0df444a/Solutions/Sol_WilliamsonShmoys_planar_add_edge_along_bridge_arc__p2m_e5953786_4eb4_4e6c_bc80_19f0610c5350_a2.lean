-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_edge_along_bridge_arc__p2m_e5953786_4eb4_4e6c_bc80_19f0610c5350_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:15:51.034526+00:00
-- url     : https://prove2.me/submissions/6e7ad9d8-ec3e-4ebb-af84-a03e813ee25e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_admissible_bridge_arc_addition_preserves_planarity__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1
import Theorems.Thm_WilliamsonShmoys_add_nonreachable_edge_graph__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hdraw : Function.Injective p ∧
      (∀ u v, u < v → G.Adj u v →
        ContinuousOn (arc u v) (Set.Icc 0 1) ∧
        Set.InjOn (arc u v) (Set.Icc 0 1) ∧
        arc u v 0 = p u ∧ arc u v 1 = p v ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
      (∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
        (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (u v : V)
    (huv : u < v ∧ ¬ G.Reachable u v)
    (c : ℝ → ℝ × ℝ)
    (hc : ContinuousOn c (Set.Icc 0 1) ∧
      Set.InjOn c (Set.Icc 0 1) ∧
      c 0 = p u ∧ c 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          c t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.Reachable u v := by
  obtain ⟨K, hGK, hreach, hKedges⟩ :=
    WilliamsonShmoys.add_nonreachable_edge_graph__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1
      G u v huv
  have hplanar :=
    WilliamsonShmoys.admissible_bridge_arc_addition_preserves_planarity__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1
      G p arc hdraw u v huv c hc K hGK hKedges
  exact ⟨K, hGK, hplanar, hreach⟩