-- Prove2me | solution 1 for WilliamsonShmoys.added_edge_bridge_meets_original_arcs_only_at_endpoints__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:15:39.836207+00:00
-- url     : https://prove2.me/submissions/13075e9b-338b-4528-a17f-3182520f581e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hAugCross : ∀ a b x y, a < b → x < y →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj x y →
      (a, b) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc a b t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hnot : ¬ H.Reachable u v)
    (bridge : ℝ → ℝ × ℝ)
    (hbridge : bridge = if u < v then arc u v else fun t => arc v u (1 - t)) :
    ∀ a b, a < b → H.Adj a b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        bridge t = arc a b s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
  have huv : u ≠ v := by
    intro huv
    subst v
    exact hnot SimpleGraph.Reachable.rfl
  intro a b hablt hab t ht s hs hint
  have hOrig : (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b := by
    rw [SimpleGraph.sup_adj]
    exact Or.inl hab
  rcases lt_or_gt_of_ne huv with huvlt | hvult
  · have hAdded : (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj u v := by
      rw [SimpleGraph.sup_adj]
      right
      simp [SimpleGraph.fromEdgeSet_adj]
      exact huv
    have hpair : (u, v) ≠ (a, b) := by
      intro heq
      have ha : u = a := congrArg Prod.fst heq
      have hb : v = b := congrArg Prod.snd heq
      subst a
      subst b
      exact hnot hab.reachable
    have hcross := hAugCross u v a b huvlt hablt hAdded hOrig hpair t ht s hs
    rw [hbridge, if_pos huvlt] at hint
    exact hcross hint
  · have hAdded : (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj v u := by
      rw [SimpleGraph.sup_adj]
      right
      simp [SimpleGraph.fromEdgeSet_adj]
      exact huv.symm
    have hpair : (v, u) ≠ (a, b) := by
      intro heq
      have ha : v = a := congrArg Prod.fst heq
      have hb : u = b := congrArg Prod.snd heq
      subst a
      subst b
      exact hnot hab.symm.reachable
    have ht' : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
      change (0 : ℝ) ≤ 1 - t ∧ 1 - t ≤ 1
      change (0 : ℝ) ≤ t ∧ t ≤ 1 at ht
      constructor <;> linarith
    have hcross := hAugCross v u a b hvult hablt hAdded hOrig hpair (1 - t) ht' s hs
    rw [hbridge, if_neg (not_lt_of_ge hvult.le)] at hint
    rcases hcross hint with ⟨htend, hsend⟩
    refine ⟨?_, hsend⟩
    rcases htend with ht0 | ht1
    · right
      linarith
    · left
      linarith