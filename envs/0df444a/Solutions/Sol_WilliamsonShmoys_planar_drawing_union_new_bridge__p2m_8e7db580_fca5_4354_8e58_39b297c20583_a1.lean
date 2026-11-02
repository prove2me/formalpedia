-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_union_new_bridge__p2m_8e7db580_fca5_4354_8e58_39b297c20583_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:04:19.048209+00:00
-- url     : https://prove2.me/submissions/d68dde4a-987f-4a5d-9cf0-0e3daaa0d45b

import Theorems.Thm_WilliamsonShmoys_planar_bridge_augmented_arc_local__p2m_3ac38dfe_f4e4_4970_8b72_a722a3a2a331_a2
import Theorems.Thm_WilliamsonShmoys_planar_bridge_augmented_arc_crossing__p2m_3ac38dfe_f4e4_4970_8b72_a722a3a2a331_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
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
    (hne : u ≠ v) (hnew : ¬ H.Adj u v) :
    HasPlanarDrawingOn
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by
  classical
  rcases hdata with ⟨p, arc, bridge, hp, hold, holdcross,
    hcont, hinj, hzero, hone, hav, hbridgecross⟩
  let augmented : V → V → ℝ → ℝ × ℝ :=
    fun a b t =>
      if u < v then
        if a = u ∧ b = v then bridge t else arc a b t
      else
        if a = v ∧ b = u then bridge (1 - t) else arc a b t
  have hdraw : Function.Injective p ∧
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
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :=
    ⟨hp, hold, holdcross⟩
  have hbridge :
      ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn bridge (Set.Icc 0 1) ∧
      bridge 0 = p u ∧
      bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :=
    ⟨hcont, hinj, hzero, hone, hav, hbridgecross⟩
  have hlocal :=
    WilliamsonShmoys.planar_bridge_augmented_arc_local__p2m_3ac38dfe_f4e4_4970_8b72_a722a3a2a331_a2
      H u v p arc bridge hne hnew hdraw hbridge
  have hcross :=
    WilliamsonShmoys.planar_bridge_augmented_arc_crossing__p2m_3ac38dfe_f4e4_4970_8b72_a722a3a2a331_a2
      H u v p arc bridge hne hnew hdraw hbridge
  exact ⟨p, augmented, hp, by simpa [augmented] using hlocal,
    by simpa [augmented] using hcross⟩