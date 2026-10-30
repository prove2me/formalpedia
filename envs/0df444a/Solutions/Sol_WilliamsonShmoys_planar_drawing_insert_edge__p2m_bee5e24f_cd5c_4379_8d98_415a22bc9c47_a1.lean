-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_insert_edge__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:51:03.188277+00:00
-- url     : https://prove2.me/submissions/7937574f-f3ec-4eab-ab45-3b0393623ed1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_insert_edge_edge_data__p2m_14525ba3_f0c8_4c45_a13f_97b8acb9dc74_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_insert_edge_crossing_data__p2m_14525ba3_f0c8_4c45_a13f_97b8acb9dc74_a2
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (u v : V)
    (gamma : ℝ → ℝ × ℝ) (huv : u < v)
    (hp : Function.Injective p ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧
      (∀ x y a b, x < y → a < b → H.Adj x y → H.Adj a b →
        (x, y) ≠ (a, b) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
          arc x y t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hgamma : ContinuousOn gamma (Set.Icc 0 1) ∧
      Set.InjOn gamma (Set.Icc 0 1) ∧ gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → H.Adj x y →
        ∀ s ∈ Set.Icc 0 1, gamma t ≠ arc x y s))
    (hchar : ∀ x y, G.Adj x y ↔
      H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    HasPlanarDrawingOn G := by
  rcases hp with ⟨hinj, hedge, hcross⟩
  let arcNew : V → V → ℝ → ℝ × ℝ :=
    fun x y t => if x = u ∧ y = v then gamma t else arc x y t
  have hpatch : ∀ x y t,
      arcNew x y t = if x = u ∧ y = v then gamma t else arc x y t := by
    intro x y t
    rfl
  refine ⟨p, arcNew, hinj, ?_, ?_⟩
  · exact WilliamsonShmoys.planar_drawing_insert_edge_edge_data__p2m_14525ba3_f0c8_4c45_a13f_97b8acb9dc74_a2
      H G p arc u v gamma huv ⟨hinj, hedge, hcross⟩ hgamma hchar arcNew hpatch
  · exact WilliamsonShmoys.planar_drawing_insert_edge_crossing_data__p2m_14525ba3_f0c8_4c45_a13f_97b8acb9dc74_a2
      H G p arc u v gamma huv ⟨hinj, hedge, hcross⟩ hgamma hchar arcNew hpatch