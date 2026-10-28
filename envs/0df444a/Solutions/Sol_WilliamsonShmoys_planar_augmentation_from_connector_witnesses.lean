-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_from_connector_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:48:30.303157+00:00
-- url     : https://prove2.me/submissions/aed644cb-51e1-4950-8f5e-488ed446df3f

import Theorems.Thm_WilliamsonShmoys_planar_augmentation_insert_graph
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_draw_connector

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (u v : V)
    (hdisconnected : ¬ Relation.ReflTransGen H.Adj u v)
    (hgeom : ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (c : ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧
      (∀ x y a b, x < y → a < b → H.Adj x y → H.Adj a b →
        (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      (ContinuousOn c (Set.Icc 0 1) ∧ Set.InjOn c (Set.Icc 0 1) ∧
        c 0 = p (min u v) ∧ c 1 = p (max u v) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) ∧
        (∀ x y, x < y → H.Adj x y → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ s ∈ Set.Icc (0 : ℝ) 1, c t = arc x y s →
            ∃ w, (w = min u v ∨ w = max u v) ∧ (w = x ∨ w = y) ∧
              ((t = 0 ∧ w = min u v) ∨ (t = 1 ∧ w = max u v)) ∧
              ((s = 0 ∧ w = x) ∨ (s = 1 ∧ w = y))))) :
    ∃ K : SimpleGraph V,
      (∀ ⦃x y⦄, H.Adj x y → K.Adj x y) ∧
      (∃ e : Sym2 V, e ∉ H.edgeSet ∧ K.edgeSet = insert e H.edgeSet) ∧
      K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  let K : SimpleGraph V :=
    SimpleGraph.fromEdgeSet (insert s(u, v) H.edgeSet)
  have hbook := WilliamsonShmoys.planar_augmentation_insert_graph H u v hdisconnected
  have hbook' :
      (∀ ⦃x y⦄, H.Adj x y → K.Adj x y) ∧
        (∃ e : Sym2 V, e ∉ H.edgeSet ∧ K.edgeSet = insert e H.edgeSet) ∧ K.Adj u v := by
    simpa [K] using hbook
  have hdraw :=
    WilliamsonShmoys.planar_augmentation_draw_connector H hH u v hdisconnected hgeom
  exact ⟨K, hbook'.1, hbook'.2.1, hbook'.2.2, by simpa [K] using hdraw⟩
