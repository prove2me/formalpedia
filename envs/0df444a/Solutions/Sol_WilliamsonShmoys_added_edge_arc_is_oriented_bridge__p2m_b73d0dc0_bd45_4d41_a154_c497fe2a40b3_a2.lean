-- Prove2me | solution 1 for WilliamsonShmoys.added_edge_arc_is_oriented_bridge__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:12:10.835048+00:00
-- url     : https://prove2.me/submissions/24ef0f17-cb80-4177-b028-db70ac3fa42c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hAugEdge : ∀ a b, a < b →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hnot : ¬ H.Reachable u v) :
    let bridge : ℝ → ℝ × ℝ := if u < v then arc u v else fun t => arc v u (1 - t)
    ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
    Set.InjOn bridge (Set.Icc 0 1) ∧
    bridge 0 = p u ∧ bridge 1 = p v ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) := by
  have huv_ne : u ≠ v := by
    intro huv
    subst v
    exact hnot (SimpleGraph.Reachable.refl u)
  by_cases huv : u < v
  · have hedge : (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj u v := by
      rw [SimpleGraph.sup_adj]
      right
      rw [SimpleGraph.fromEdgeSet_adj]
      simp [huv_ne]
    rcases hAugEdge u v huv hedge with ⟨hcont, hinj, hzero, hone, havoid⟩
    simpa [huv] using And.intro hcont (And.intro hinj (And.intro hzero (And.intro hone havoid)))
  · have hvu : v < u := lt_of_le_of_ne (le_of_not_gt huv) (Ne.symm huv_ne)
    have hedge : (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj v u := by
      rw [SimpleGraph.sup_adj]
      right
      rw [SimpleGraph.fromEdgeSet_adj]
      simp [Ne.symm huv_ne]
    rcases hAugEdge v u hvu hedge with ⟨hcont, hinj, hzero, hone, havoid⟩
    have hflipCont : ContinuousOn (fun t : ℝ => 1 - t) (Set.Icc 0 1) := by
      fun_prop
    have hflipMaps : Set.MapsTo (fun t : ℝ => 1 - t) (Set.Icc 0 1) (Set.Icc 0 1) := by
      intro t ht
      rcases ht with ⟨ht0, ht1⟩
      constructor
      · linarith
      · linarith
    have hflipInj : Set.InjOn (fun t : ℝ => 1 - t) (Set.Icc 0 1) := by
      intro x hx y hy hxy
      linarith
    have hbridgeCont : ContinuousOn (fun t : ℝ => arc v u (1 - t)) (Set.Icc 0 1) := by
      exact hcont.comp' hflipCont hflipMaps
    have hbridgeInj : Set.InjOn (fun t : ℝ => arc v u (1 - t)) (Set.Icc 0 1) := by
      exact hinj.comp hflipInj hflipMaps
    have hbridgeZero : (fun t : ℝ => arc v u (1 - t)) 0 = p u := by
      simpa using hone
    have hbridgeOne : (fun t : ℝ => arc v u (1 - t)) 1 = p v := by
      simpa using hzero
    have hbridgeAvoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w,
        (fun t : ℝ => arc v u (1 - t)) t ≠ p w := by
      intro t ht w
      rcases ht with ⟨ht0, ht1⟩
      have hmiddle : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor
        · linarith
        · linarith
      simpa using havoid (1 - t) hmiddle w
    simpa [huv] using And.intro hbridgeCont
      (And.intro hbridgeInj (And.intro hbridgeZero (And.intro hbridgeOne hbridgeAvoid)))