-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_union_of_bridge_setup__p2m_6b761602_ec4e_4b71_82d8_bcea18a590f0_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:53:30.096413+00:00
-- url     : https://prove2.me/submissions/05dc8ae8-2f99-4447-ad10-216a19aaf6b7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_union_of_bridge_setup_nondegenerate__p2m_ca2a92bc_8b5e_4bfc_b135_48ef776a9947_a2

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
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) :
    HasPlanarDrawingOn
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by
  by_cases huv : u = v
  · rcases hdata with ⟨p, arc, bridge, hp, hedge, hpair, hcont, hinj,
      hzero, hone, hav, hcross⟩
    have h01 : (0 : ℝ) = 1 := by
      apply hinj (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      calc
        bridge 0 = p u := hzero
        _ = p v := congrArg p huv
        _ = bridge 1 := hone.symm
    norm_num at h01
  · exact WilliamsonShmoys.planar_drawing_union_of_bridge_setup_nondegenerate__p2m_ca2a92bc_8b5e_4bfc_b135_48ef776a9947_a2
      H u v hdata huv