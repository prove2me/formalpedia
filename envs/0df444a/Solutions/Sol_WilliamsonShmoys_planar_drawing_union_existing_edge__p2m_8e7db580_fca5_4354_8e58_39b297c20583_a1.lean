-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_union_existing_edge__p2m_8e7db580_fca5_4354_8e58_39b297c20583_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:44:27.242736+00:00
-- url     : https://prove2.me/submissions/d37b8894-e73d-4625-bf78-a67bcbc00d00

import Mathlib
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
    (hne : u ≠ v) (hedge : H.Adj u v) :
    HasPlanarDrawingOn
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by
  have hEq : H ⊔ SimpleGraph.edge u v = H := by
    ext a b
    simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
    constructor
    · rintro (hab | ⟨hpair, _⟩)
      · exact hab
      · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hedge
        · exact hedge.symm
    · intro hab
      exact Or.inl hab
  change HasPlanarDrawingOn (H ⊔ SimpleGraph.edge u v)
  rw [hEq]
  rcases hdata with ⟨p, arc, bridge, hinj, harc, hcross, _, _, _, _, _, _⟩
  exact ⟨p, arc, hinj, harc, hcross⟩