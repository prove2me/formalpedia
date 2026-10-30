-- Prove2me | solution 1 for WilliamsonShmoys.bridge_curve_meets_original_edges__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:09.428657+00:00
-- url     : https://prove2.me/submissions/9f118a1d-5b79-4a16-906f-3cd79323c65e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (x y : V)
    (hxy : ¬ G.Reachable x y)
    (hrel : ∀ u v, H.Adj u v ↔
      G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))
    (arc : V → V → ℝ → ℝ × ℝ)
    (hcross : ∀ u v a b, u < v → a < b → H.Adj u v → H.Adj a b →
      (u, v) ≠ (a, b) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc u v t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (γ : ℝ → ℝ × ℝ)
    (hrep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ t = if x < y then arc x y t else arc y x (1 - t)) :
    ∀ u v, u < v → G.Adj u v →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        γ t = arc u v s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
  intro u v huv hadj t ht s hs hEq
  have hxne : x ≠ y := by
    intro hxyEq
    have hloop : H.Adj x x := (hrel x x).2 (Or.inr (Or.inl ⟨rfl, hxyEq⟩))
    exact H.irrefl hloop
  by_cases hxyord : x < y
  · have hadd : H.Adj x y := (hrel x y).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hdistinct : (x, y) ≠ (u, v) := by
      intro heq
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact hxy (SimpleGraph.Adj.reachable hadj)
    have hcurve : arc x y t = arc u v s := by
      have hrep' := hrep t ht
      simpa [hxyord] using hrep'.symm.trans hEq
    exact hcross x y u v hxyord huv hadd ((hrel u v).2 (Or.inl hadj))
      hdistinct t ht s hs hcurve
  · have hyxord : y < x := lt_of_le_of_ne (le_of_not_gt hxyord) (Ne.symm hxne)
    have hadd : H.Adj y x := (hrel y x).2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
    have hdistinct : (y, x) ≠ (u, v) := by
      intro heq
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact hxy (SimpleGraph.Adj.reachable hadj.symm)
    have hr : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · simp only [Set.mem_Icc] at ht
        linarith
      · simp only [Set.mem_Icc] at ht
        linarith
    have hrep' : γ t = arc y x (1 - t) := by
      simpa [hxyord] using hrep t ht
    have hcurve : arc y x (1 - t) = arc u v s := hrep'.symm.trans hEq
    have hc := hcross y x u v hyxord huv hadd ((hrel u v).2 (Or.inl hadj))
      hdistinct (1 - t) hr s hs hcurve
    rcases hc with ⟨ht', hs'⟩
    rcases ht' with ht' | ht'
    · have ht1 : t = 1 := by linarith
      exact ⟨Or.inr ht1, hs'⟩
    · have ht0 : t = 0 := by linarith
      exact ⟨Or.inl ht0, hs'⟩