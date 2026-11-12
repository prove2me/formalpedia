-- Prove2me | solution 1 for RemovingTrees.Main.fundamental_cuts_noncrossing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:42:50.081415+00:00
-- url     : https://prove2.me/submissions/981834a7-7f1e-4bec-b9ce-3d6b2b3f611a

import Mathlib
import Definitions.Def_RemovingTrees_Main_GraphModel

section
set_option autoImplicit false

namespace RemovingTrees.Dev.Noncrossing
open RemovingTrees.Main

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key (l1 r1 l2 r2 : Bool × Bool)
    (h1 : l1.1 ≠ r1.1) (h2 : l2.2 ≠ r2.2)
    (h12 : l1.2 ≠ r1.2 → (l1 = l2 ∧ r1 = r2)) (h21 : l2.1 ≠ r2.1 → (l2 = l1 ∧ r2 = r1))
    (cov : ∀ x : Bool × Bool, ¬((l1 = x) ↔ (r1 = x)) ∨ ¬((l2 = x) ↔ (r2 = x))) : False := by
  revert l1 r1 l2 r2
  decide

theorem noncrossing {n m : ℕ} (G : MultiGraph n m) (hn : 2 ≤ n)
    (T : Finset (Fin m)) (hT : Tree G T) (S₁ S₂ : Finset (Fin n))
    (h₁ : (cut G T S₁).card = 1) (h₂ : (cut G T S₂).card = 1) :
    ¬ Cross S₁ S₂ := by
  intro hc
  obtain ⟨hAB, hBA, hI, hD⟩ := hc
  obtain ⟨e1, he1⟩ := Finset.card_eq_one.mp h₁
  obtain ⟨e2, he2⟩ := Finset.card_eq_one.mp h₂
  let reg : Fin n → Bool × Bool := fun v => (decide (v ∈ S₁), decide (v ∈ S₂))
  have hne : ∀ x : Bool × Bool, ∃ v, reg v = x := by
    intro x
    rcases x with ⟨a, b⟩
    cases a <;> cases b
    · obtain ⟨v, hv⟩ := hD; exact ⟨v, by simp [reg] at hv ⊢; simp [hv]⟩
    · obtain ⟨v, hv⟩ := hBA; exact ⟨v, by simp [reg] at hv ⊢; simp [hv]⟩
    · obtain ⟨v, hv⟩ := hAB; exact ⟨v, by simp [reg] at hv ⊢; simp [hv]⟩
    · obtain ⟨v, hv⟩ := hI; exact ⟨v, by simp [reg] at hv ⊢; simp [hv]⟩
  have mem1 : ∀ e, e ∈ cut G T S₁ ↔ e = e1 := by
    intro e; rw [he1]; simp
  have mem2 : ∀ e, e ∈ cut G T S₂ ↔ e = e2 := by
    intro e; rw [he2]; simp
  have e1T : e1 ∈ cut G T S₁ := (mem1 e1).2 rfl
  have e2T : e2 ∈ cut G T S₂ := (mem2 e2).2 rfl
  have e1T' : e1 ∈ T := (Finset.mem_filter.mp e1T).1
  have e2T' : e2 ∈ T := (Finset.mem_filter.mp e2T).1
  -- crossing predicate as xor of region membership
  have crossIff : ∀ (S : Finset (Fin n)) (e : Fin m), (e ∈ cut G T S ↔
      (e ∈ T ∧ ((G.left e ∈ S) ≠ (G.right e ∈ S)))) := by
    intro S e
    simp only [cut, Finset.mem_filter]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨h, ?_⟩
      rcases h' with ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b]
    · rintro ⟨h, h'⟩
      refine ⟨h, ?_⟩
      by_cases a : G.left e ∈ S <;> by_cases b : G.right e ∈ S <;> simp_all
  have cov : ∀ x : Bool × Bool,
      ¬((reg (G.left e1) = x) ↔ (reg (G.right e1) = x)) ∨
      ¬((reg (G.left e2) = x) ↔ (reg (G.right e2) = x)) := by
    intro x
    let X : Finset (Fin n) := Finset.univ.filter (fun v => reg v = x)
    have hX : NontrivialShore X := by
      refine ⟨?_, ?_⟩
      · obtain ⟨v, hv⟩ := hne x
        exact ⟨v, by simp [X, hv]⟩
      · intro h
        obtain ⟨v, hv⟩ := hne (!x.1, x.2)
        have : v ∈ X := by rw [h]; exact Finset.mem_univ _
        simp only [X, Finset.mem_filter] at this
        have := this.2
        rw [hv] at this
        have := congrArg Prod.fst this
        simp at this
    obtain ⟨e, he⟩ := hT.1 X hX
    have heT : e ∈ T := (Finset.mem_filter.mp he).1
    have hX' := (crossIff X e).1 he
    have hXe : ¬((reg (G.left e) = x) ↔ (reg (G.right e) = x)) := by
      have := hX'.2
      simpa [X] using this
    by_cases c1 : e ∈ cut G T S₁
    · have := (mem1 e).1 c1
      subst this; exact Or.inl hXe
    by_cases c2 : e ∈ cut G T S₂
    · have := (mem2 e).1 c2
      subst this; exact Or.inr hXe
    exfalso
    rw [crossIff] at c1 c2
    have a1 : (G.left e ∈ S₁) = (G.right e ∈ S₁) := by
      by_contra h; exact c1 ⟨heT, h⟩
    have a2 : (G.left e ∈ S₂) = (G.right e ∈ S₂) := by
      by_contra h; exact c2 ⟨heT, h⟩
    have : reg (G.left e) = reg (G.right e) := by
      simp [reg, a1, a2]
    exact hXe (by rw [this])
  have f1 := (crossIff S₁ e1).1 e1T
  have f2 := (crossIff S₂ e2).1 e2T
  refine key (reg (G.left e1)) (reg (G.right e1)) (reg (G.left e2)) (reg (G.right e2))
    ?_ ?_ ?_ ?_ cov
  · simpa [reg] using f1.2
  · simpa [reg] using f2.2
  · intro h
    have hm : e1 ∈ cut G T S₂ := by
      rw [crossIff]; refine ⟨e1T', ?_⟩; simpa [reg] using h
    have := (mem2 e1).1 hm
    subst this; exact ⟨rfl, rfl⟩
  · intro h
    have hm : e2 ∈ cut G T S₁ := by
      rw [crossIff]; refine ⟨e2T', ?_⟩; simpa [reg] using h
    have := (mem1 e2).1 hm
    subst this; exact ⟨rfl, rfl⟩

end RemovingTrees.Dev.Noncrossing

namespace RemovingTrees.Main
theorem chk_fundamental_cuts_noncrossing {n m : ℕ} (G : MultiGraph n m) (hn : 2 ≤ n)
    (T : Finset (Fin m)) (hT : Tree G T) (S₁ S₂ : Finset (Fin n))
    (h₁ : (cut G T S₁).card = 1) (h₂ : (cut G T S₂).card = 1) :
    ¬ Cross S₁ S₂ := RemovingTrees.Dev.Noncrossing.noncrossing G hn T hT S₁ S₂ h₁ h₂
end RemovingTrees.Main
end

theorem solution : type_of% @RemovingTrees.Main.chk_fundamental_cuts_noncrossing := @RemovingTrees.Main.chk_fundamental_cuts_noncrossing
