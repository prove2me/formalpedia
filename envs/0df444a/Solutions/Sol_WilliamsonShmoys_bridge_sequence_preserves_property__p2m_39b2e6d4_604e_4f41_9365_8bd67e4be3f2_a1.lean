-- Prove2me | solution 1 for WilliamsonShmoys.bridge_sequence_preserves_property__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:51.059364+00:00
-- url     : https://prove2.me/submissions/69f9aae9-b121-4605-88a2-edaa0ebc935f

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P M)
    (hbridge : ∀ (G : SimpleGraph V), P G →
      ∀ x y : V, ¬ G.Reachable x y →
        ∃ N : SimpleGraph V,
          G ≤ N ∧
          (∀ u v, N.Adj u v ↔
            G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) ∧
          P N)
    (n : Nat)
    (f : Fin (n + 1) → SimpleGraph V)
    (hstart : f 0 = M)
    (hstep : ∀ i : Fin n, ∃ x y : V,
      ¬ (f i.castSucc).Reachable x y ∧
      ∀ u v,
        (f i.succ).Adj u v ↔
          (f i.castSucc).Adj u v ∨
            ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) :
    M ≤ f (Fin.last n) ∧ P (f (Fin.last n)) := by
  revert f
  induction n with
  | zero =>
      intro f hstart hstep
      have hlast : Fin.last 0 = 0 := rfl
      rw [hlast, hstart]
      exact ⟨le_rfl, hP⟩
  | succ n ih =>
      intro f hstart hstep
      let g : Fin (n + 1) → SimpleGraph V := fun i => f i.castSucc
      have hgstart : g 0 = M := by
        change f (0 : Fin (n + 1)).castSucc = M
        simpa using hstart
      have hgstep : ∀ i : Fin n, ∃ x y : V,
          ¬ (g i.castSucc).Reachable x y ∧
          ∀ u v,
            (g i.succ).Adj u v ↔
              (g i.castSucc).Adj u v ∨
                ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) := by
        intro i
        rcases hstep i.castSucc with ⟨x, y, hreach, hadj⟩
        refine ⟨x, y, ?_, ?_⟩
        · change ¬ (f (i.castSucc).castSucc).Reachable x y
          exact hreach
        · intro u v
          have hi : (i.castSucc).succ = i.succ.castSucc := by
            apply Fin.ext
            rfl
          change (f (i.succ).castSucc).Adj u v ↔
            (f (i.castSucc).castSucc).Adj u v ∨
              ((u = x ∧ v = y) ∨ (u = y ∧ v = x))
          rw [← hi]
          exact hadj u v
      have hprev := ih g hgstart hgstep
      rcases hstep (Fin.last n) with ⟨x, y, hreach, hadj⟩
      rcases hbridge (g (Fin.last n)) hprev.2 x y hreach with
        ⟨N, hsub, hNadj, hPN⟩
      have hidx : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      have hadj' : ∀ u v,
          (f (Fin.last (n + 1))).Adj u v ↔
            (f (Fin.last n).castSucc).Adj u v ∨
              ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) := by
        intro u v
        rw [← hidx]
        exact hadj u v
      have hEq : N = f (Fin.last (n + 1)) := by
        ext u v
        exact (hNadj u v).trans (hadj' u v).symm
      have hfinal : g (Fin.last n) ≤ f (Fin.last (n + 1)) := by
        rw [hEq] at hsub
        exact hsub
      constructor
      · exact le_trans hprev.1 hfinal
      · rw [← hEq]
        exact hPN