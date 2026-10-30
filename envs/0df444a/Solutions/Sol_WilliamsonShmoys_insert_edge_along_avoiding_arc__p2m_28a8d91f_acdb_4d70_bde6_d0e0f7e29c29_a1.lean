-- Prove2me | solution 1 for WilliamsonShmoys.insert_edge_along_avoiding_arc__p2m_28a8d91f_acdb_4d70_bde6_d0e0f7e29c29_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:59.489654+00:00
-- url     : https://prove2.me/submissions/76a6abf9-f52d-4f92-b5ef-68f2003d9a4f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_insert_edge_graph_exists__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_insert_edge__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧
      (∀ x y a b, x < y → a < b → H.Adj x y → H.Adj a b →
        (x, y) ≠ (a, b) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (u v : V) (gamma : ℝ → ℝ × ℝ) (huv : u < v) (hnot : ¬ H.Adj u v)
    (hgamma : ContinuousOn gamma (Set.Icc 0 1) ∧
      Set.InjOn gamma (Set.Icc 0 1) ∧ gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → H.Adj x y →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s)) :
    ∃ G : SimpleGraph V, H ≤ G ∧ ∃ a b : V,
      a ≠ b ∧ ¬ H.Adj a b ∧ G.Adj a b ∧ HasPlanarDrawingOn G := by
  obtain ⟨G, hHG, hGuv, hchar⟩ :=
    WilliamsonShmoys.insert_edge_graph_exists__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a1
      H u v
  refine ⟨G, hHG, u, v, ne_of_lt huv, hnot, hGuv, ?_⟩
  exact WilliamsonShmoys.planar_drawing_insert_edge__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a1
    H G p arc u v gamma huv hp hgamma hchar