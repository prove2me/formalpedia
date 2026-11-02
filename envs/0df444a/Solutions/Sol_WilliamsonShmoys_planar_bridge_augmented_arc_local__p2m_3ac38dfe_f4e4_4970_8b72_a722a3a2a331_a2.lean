-- Prove2me | solution 1 for WilliamsonShmoys.planar_bridge_augmented_arc_local__p2m_3ac38dfe_f4e4_4970_8b72_a722a3a2a331_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:22:48.006464+00:00
-- url     : https://prove2.me/submissions/29c34fc8-763f-4432-a000-02f6ec7904e0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (bridge : ℝ → ℝ × ℝ)
    (hne : u ≠ v) (hnew : ¬ H.Adj u v)
    (hdraw : Function.Injective p ∧
      (∀ a b, a < b → H.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
        (a, b) ≠ (x, y) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc a b t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hbridge : ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn bridge (Set.Icc 0 1) ∧ bridge 0 = p u ∧ bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) :
    ∀ a b, a < b →
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Adj a b →
      ContinuousOn
        ((fun a b t => if u < v then
          if a = u ∧ b = v then bridge t else arc a b t
        else if a = v ∧ b = u then bridge (1 - t) else arc a b t) a b)
        (Set.Icc 0 1) ∧
      Set.InjOn
        ((fun a b t => if u < v then
          if a = u ∧ b = v then bridge t else arc a b t
        else if a = v ∧ b = u then bridge (1 - t) else arc a b t) a b)
        (Set.Icc 0 1) ∧
      (fun a b t => if u < v then
        if a = u ∧ b = v then bridge t else arc a b t
      else if a = v ∧ b = u then bridge (1 - t) else arc a b t) a b 0 = p a ∧
      (fun a b t => if u < v then
        if a = u ∧ b = v then bridge t else arc a b t
      else if a = v ∧ b = u then bridge (1 - t) else arc a b t) a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w,
        (fun a b t => if u < v then
          if a = u ∧ b = v then bridge t else arc a b t
        else if a = v ∧ b = u then bridge (1 - t) else arc a b t) a b t ≠ p w := by
  intro a b hab hadj
  have hsplit : H.Adj a b ∨ (s(a, b) = s(u, v) ∧ a ≠ b) := by
    simpa only [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj,
      Set.mem_singleton_iff] using hadj
  rcases hsplit with hold | ⟨hedge, _⟩
  · by_cases huv : u < v
    · have hnot : ¬ (a = u ∧ b = v) := by
        rintro ⟨rfl, rfl⟩
        exact hnew hold
      have hprops := hdraw.2.1 a b hab hold
      simpa [huv, hnot] using hprops
    · have hnot : ¬ (a = v ∧ b = u) := by
        rintro ⟨rfl, rfl⟩
        exact hnew ((H.adj_comm a b).mp hold)
      have hprops := hdraw.2.1 a b hab hold
      simpa [huv, hnot] using hprops
  · rcases (Sym2.eq_iff.mp hedge) with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
    · subst a
      subst b
      by_cases huv : u < v
      · simpa [huv] using
          (show ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
            Set.InjOn bridge (Set.Icc 0 1) ∧ bridge 0 = p u ∧
            bridge 1 = p v ∧
            ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w from
            ⟨hbridge.1, hbridge.2.1, hbridge.2.2.1, hbridge.2.2.2.1,
              hbridge.2.2.2.2.1⟩)
      · exact (huv hab).elim
    · subst a
      subst b
      by_cases huv : u < v
      · have hvu : v < u := by simpa using hab
        exact (lt_asymm huv hvu).elim
      · have hvu : v < u := lt_of_le_of_ne (le_of_not_gt huv) (Ne.symm hne)
        have hrcc : Set.MapsTo (fun t : ℝ => 1 - t)
            (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1) := by
          intro t ht
          rcases ht with ⟨ht0, ht1⟩
          change 0 ≤ 1 - t ∧ 1 - t ≤ 1
          constructor <;> linarith
        have hroo : Set.MapsTo (fun t : ℝ => 1 - t)
            (Set.Ioo (0 : ℝ) 1) (Set.Ioo 0 1) := by
          intro t ht
          rcases ht with ⟨ht0, ht1⟩
          change 0 < 1 - t ∧ 1 - t < 1
          constructor <;> linarith
        have hrcont : ContinuousOn (fun t : ℝ => 1 - t) (Set.Icc (0 : ℝ) 1) := by
          fun_prop
        have hrev :
            ContinuousOn (fun t : ℝ => bridge (1 - t)) (Set.Icc (0 : ℝ) 1) ∧
            Set.InjOn (fun t : ℝ => bridge (1 - t)) (Set.Icc 0 1) ∧
            (fun t : ℝ => bridge (1 - t)) 0 = p v ∧
            (fun t : ℝ => bridge (1 - t)) 1 = p u ∧
            ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge (1 - t) ≠ p w := by
          refine ⟨hbridge.1.comp hrcont hrcc, ?_, ?_, ?_, ?_⟩
          · intro x hx y hy hxy
            have heq := hbridge.2.1 (hrcc hx) (hrcc hy) hxy
            linarith
          · simpa using hbridge.2.2.2.1
          · simpa using hbridge.2.2.1
          · intro t ht w
            exact hbridge.2.2.2.2.1 (1 - t) (hroo ht) w
        simpa [huv] using hrev
