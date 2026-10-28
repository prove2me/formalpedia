-- Prove2me | solution 1 for WilliamsonShmoys.crossing_free_drawing_add_edge_along_arc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:11:55.665403+00:00
-- url     : https://prove2.me/submissions/824aeacf-bf93-4a86-95aa-c42ce5edaaa3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_fresh_arc_addition

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hbase : Function.Injective p ∧
      (∀ x y, x < y → G.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)) ∧
      (∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
        (x, y) ≠ (a, b) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (γ : ℝ → ℝ × ℝ)
    (hγcont : ContinuousOn γ (Set.Icc 0 1))
    (hγinj : Set.InjOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = p u) (hγ1 : γ 1 = p v)
    (hγvert : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (hγedge : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        γ t ≠ arc x y s) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ H.Adj u v := by
  by_cases hadj : G.Adj u v
  · exact ⟨G, le_rfl, ⟨p, arc, hbase⟩, hadj⟩
  · exact WilliamsonShmoys.fresh_arc_addition G u v huv p arc hbase γ
      hγcont hγinj hγ0 hγ1 hγvert hγedge hadj