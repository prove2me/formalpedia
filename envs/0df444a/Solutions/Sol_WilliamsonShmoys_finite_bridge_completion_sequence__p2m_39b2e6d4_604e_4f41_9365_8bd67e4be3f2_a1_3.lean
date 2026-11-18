-- Prove2me | solution 3 for WilliamsonShmoys.finite_bridge_completion_sequence__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:11:43.416733+00:00
-- url     : https://prove2.me/submissions/c7f6e995-881f-4d29-9be8-eca9f0126119

import Mathlib

set_option autoImplicit false

theorem ws_bridge_core {V : Type} [Fintype V] :
    ∀ (k : ℕ) (M : SimpleGraph V),
      {p : V × V | ¬ M.Reachable p.1 p.2}.ncard = k →
    ∃ (n : Nat) (f : Fin (n + 1) → SimpleGraph V),
      f 0 = M ∧
      (∀ x y : V, (f (Fin.last n)).Reachable x y) ∧
      (∀ i : Fin n, ∃ x y : V,
        ¬ (f i.castSucc).Reachable x y ∧
        ∀ u v : V,
          (f i.succ).Adj u v ↔
            (f i.castSucc).Adj u v ∨
              ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro M hk
    by_cases hall : ∀ x y : V, M.Reachable x y
    · exact ⟨0, fun _ => M, rfl, hall, fun i => i.elim0⟩
    · simp only [not_forall] at hall
      obtain ⟨x, y, hxy⟩ := hall
      have hne : x ≠ y := fun h => hxy (h ▸ SimpleGraph.Reachable.refl x)
      set M' := M ⊔ SimpleGraph.edge x y with hM'
      have hadj : ∀ u v : V, M'.Adj u v ↔ M.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) := by
        intro u v
        rw [hM', SimpleGraph.sup_adj, SimpleGraph.edge_adj]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · refine Or.inr ⟨h, ?_⟩
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hne
            · exact hne.symm
      have hle : M ≤ M' := le_sup_left
      have hsub : {p : V × V | ¬ M'.Reachable p.1 p.2} ⊂ {p : V × V | ¬ M.Reachable p.1 p.2} := by
        rw [Set.ssubset_iff_of_subset]
        · refine ⟨(x, y), hxy, ?_⟩
          simp only [Set.mem_setOf_eq, not_not]
          exact SimpleGraph.Adj.reachable ((hadj x y).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        · intro p hp
          simp only [Set.mem_setOf_eq] at hp ⊢
          exact fun h => hp (h.mono hle)
      have hlt := Set.ncard_lt_ncard hsub (Set.toFinite _)
      rw [hk] at hlt
      obtain ⟨n, f, hf0, hlast, hstep⟩ := ih _ hlt M' rfl
      refine ⟨n + 1, Fin.cons M f, rfl, ?_, ?_⟩
      · intro a b
        have : (Fin.last (n + 1) : Fin (n + 2)) = (Fin.last n).succ := (Fin.succ_last n).symm
        rw [this, Fin.cons_succ]
        exact hlast a b
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · refine ⟨x, y, ?_, ?_⟩
          · exact hxy
          · intro u v
            simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one, hf0]
            exact hadj u v
        · obtain ⟨a, b, h1, h2⟩ := hstep j
          refine ⟨a, b, ?_, ?_⟩
          · rw [← Fin.succ_castSucc, Fin.cons_succ]
            exact h1
          · intro u v
            rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
            exact h2 u v

theorem WilliamsonShmoys.finite_bridge_completion_sequence__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) :
    ∃ (n : Nat) (f : Fin (n + 1) → SimpleGraph V),
      f 0 = M ∧
      (∀ x y : V, (f (Fin.last n)).Reachable x y) ∧
      (∀ i : Fin n, ∃ x y : V,
        ¬ (f i.castSucc).Reachable x y ∧
        ∀ u v : V,
          (f i.succ).Adj u v ↔
            (f i.castSucc).Adj u v ∨
              ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) :=
  ws_bridge_core _ M rfl

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) :
    ∃ (n : Nat) (f : Fin (n + 1) → SimpleGraph V),
      f 0 = M ∧
      (∀ x y : V, (f (Fin.last n)).Reachable x y) ∧
      (∀ i : Fin n, ∃ x y : V,
        ¬ (f i.castSucc).Reachable x y ∧
        ∀ u v : V,
          (f i.succ).Adj u v ↔
            (f i.castSucc).Adj u v ∨
              ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) :=
  ws_bridge_core _ M rfl
