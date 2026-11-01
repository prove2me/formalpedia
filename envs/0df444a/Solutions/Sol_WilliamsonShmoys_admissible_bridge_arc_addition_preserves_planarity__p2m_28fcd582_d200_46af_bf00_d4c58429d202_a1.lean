-- Prove2me | solution 1 for WilliamsonShmoys.admissible_bridge_arc_addition_preserves_planarity__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:23:04.585384+00:00
-- url     : https://prove2.me/submissions/0aa91eff-9e40-4927-a99c-a51b1996e514

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hdraw : Function.Injective p ∧
      (∀ u v, u < v → G.Adj u v →
        ContinuousOn (arc u v) (Set.Icc 0 1) ∧
        Set.InjOn (arc u v) (Set.Icc 0 1) ∧
        arc u v 0 = p u ∧ arc u v 1 = p v ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
      (∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
        (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (u v : V)
    (huv : u < v ∧ ¬ G.Reachable u v)
    (c : ℝ → ℝ × ℝ)
    (hc : ContinuousOn c (Set.Icc 0 1) ∧
      Set.InjOn c (Set.Icc 0 1) ∧
      c 0 = p u ∧ c 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1,
          c t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (K : SimpleGraph V)
    (hGK : G ≤ K)
    (hKedges : ∀ x y, x < y →
      (K.Adj x y ↔ (G.Adj x y ∨ (x = u ∧ y = v)))) :
    WilliamsonShmoys.HasPlanarDrawingOn K := by
  rcases hdraw with ⟨hpinj, hold, hdisj⟩
  rcases hc with ⟨hccont, hcinj, hc0, hc1, hcvert, hccross⟩
  have hNoAdj : ¬ G.Adj u v := by
    intro h
    exact huv.2 h.reachable
  let newArc : V → V → ℝ → ℝ × ℝ :=
    fun x y t => if x = u ∧ y = v then c t else arc x y t
  have notNew_of_adj {x y : V} (h : G.Adj x y) :
      ¬ (x = u ∧ y = v) := by
    intro hxy
    rcases hxy with ⟨rfl, rfl⟩
    exact hNoAdj h
  refine ⟨p, newArc, hpinj, ?_, ?_⟩
  · intro x y hxy hKxy
    rcases (hKedges x y hxy).mp hKxy with hGxy | hnew
    · have hnotnew := notNew_of_adj hGxy
      simpa [newArc, hnotnew] using hold x y hxy hGxy
    · rcases hnew with ⟨hx, hy⟩
      subst x
      subst y
      simpa [newArc] using
        (show ContinuousOn c (Set.Icc 0 1) ∧
          Set.InjOn c (Set.Icc 0 1) ∧
          c 0 = p u ∧ c 1 = p v ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w from
          ⟨hccont, hcinj, hc0, hc1, hcvert⟩)
  · intro x y z w hxy hzw hKxy hKzw hne t ht s hs heq
    rcases (hKedges x y hxy).mp hKxy with hGxy | hnewxy
    · rcases (hKedges z w hzw).mp hKzw with hGzw | hnewzw
      · have hnotxy := notNew_of_adj hGxy
        have hnotzw := notNew_of_adj hGzw
        have heq' : arc x y t = arc z w s := by
          simpa [newArc, hnotxy, hnotzw] using heq
        exact hdisj x y z w hxy hzw hGxy hGzw hne t ht s hs heq'
      · rcases hnewzw with ⟨hz, hw⟩
        subst z
        subst w
        have hnotxy := notNew_of_adj hGxy
        have heq' : c s = arc x y t := by
          simpa [newArc, hnotxy] using heq.symm
        rcases hccross x y hxy hGxy s hs t ht heq' with ⟨hsends, htends⟩
        exact ⟨htends, hsends⟩
    · rcases hnewxy with ⟨hx, hy⟩
      subst x
      subst y
      rcases (hKedges z w hzw).mp hKzw with hGzw | hnewzw
      · have hnotzw := notNew_of_adj hGzw
        have heq' : c t = arc z w s := by
          simpa [newArc, hnotzw] using heq
        exact hccross z w hzw hGzw t ht s hs heq'
      · rcases hnewzw with ⟨hz, hw⟩
        subst z
        subst w
        exact (hne rfl).elim
