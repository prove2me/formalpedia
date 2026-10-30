-- Prove2me | solution 1 for WilliamsonShmoys.edge_enumeration__p2m_5afb1874_83c6_4429_86a3_ce5c27512c9e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:48:11.649064+00:00
-- url     : https://prove2.me/submissions/cf842590-6ba0-4a40-b9a2-f4feabf3f3bb

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M H : SimpleGraph V) (hMH : M ≤ H) :
    ∃ (n : Nat) (e : Fin n → V × V),
      (∀ i, (e i).1 < (e i).2) ∧
      (∀ i, H.Adj (e i).1 (e i).2 ∧ ¬ M.Adj (e i).1 (e i).2) ∧
      (∀ i j, i ≠ j → e i ≠ e j) ∧
      (∀ u v, H.Adj u v → M.Adj u v ∨
        ∃ i, ((u = (e i).1 ∧ v = (e i).2) ∨ (u = (e i).2 ∧ v = (e i).1))) := by
  classical
  let alpha : Type :=
    {p : V × V // p.1 < p.2 ∧ H.Adj p.1 p.2 ∧ ¬ M.Adj p.1 p.2}
  let q : alpha ≃ Fin (Fintype.card alpha) := Fintype.equivFin alpha
  refine ⟨Fintype.card alpha, fun i => (q.symm i).1, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (q.symm i).2.1
  · intro i
    exact ⟨(q.symm i).2.2.1, (q.symm i).2.2.2⟩
  · intro i j hij heq
    exact hij (q.symm.injective (Subtype.ext heq))
  · intro u v huv
    by_cases hM : M.Adj u v
    · exact Or.inl hM
    · right
      have hne : u ≠ v := huv.ne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · let p : alpha := ⟨(u, v), ⟨hlt, ⟨huv, hM⟩⟩⟩
        refine ⟨q p, Or.inl ?_⟩
        have hp : q.symm (q p) = p := q.symm_apply_apply p
        change u = (q.symm (q p)).1.1 ∧ v = (q.symm (q p)).1.2
        rw [hp]
        exact ⟨rfl, rfl⟩
      · have hvu : H.Adj v u := huv.symm
        have hmvu : ¬ M.Adj v u := fun hvuM => hM (hvuM.symm)
        let p : alpha := ⟨(v, u), ⟨hgt, ⟨hvu, hmvu⟩⟩⟩
        refine ⟨q p, Or.inr ?_⟩
        have hp : q.symm (q p) = p := q.symm_apply_apply p
        change u = (q.symm (q p)).1.2 ∧ v = (q.symm (q p)).1.1
        rw [hp]
        exact ⟨rfl, rfl⟩