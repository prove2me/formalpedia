-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_union_of_bridge_setup_nondegenerate__p2m_ca2a92bc_8b5e_4bfc_b135_48ef776a9947_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:11:48.943421+00:00
-- url     : https://prove2.me/submissions/e2075a94-7364-43dd-bd13-5cf492c92864

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_union_existing_edge__p2m_8e7db580_fca5_4354_8e58_39b297c20583_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_union_new_bridge__p2m_8e7db580_fca5_4354_8e58_39b297c20583_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (hdata : ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
      (bridge : ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ a b, a < b → H.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧
        arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
        (a, b) ≠ (x, y) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc a b t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn bridge (Set.Icc 0 1) ∧
      bridge 0 = p u ∧
      bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hne : u ≠ v) :
    HasPlanarDrawingOn
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by
  by_cases hedge : H.Adj u v
  · exact WilliamsonShmoys.planar_drawing_union_existing_edge__p2m_8e7db580_fca5_4354_8e58_39b297c20583_a1
      H u v hdata hne hedge
  · exact WilliamsonShmoys.planar_drawing_union_new_bridge__p2m_8e7db580_fca5_4354_8e58_39b297c20583_a1
      H u v hdata hne hedge