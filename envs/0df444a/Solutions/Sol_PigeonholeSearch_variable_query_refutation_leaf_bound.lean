-- Prove2me | solution 1 for PigeonholeSearch.variable_query_refutation_leaf_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T02:37:52.198639+00:00
-- url     : https://prove2.me/submissions/ee480fc7-3932-4ef3-8721-d8fb54d70b1d

import Definitions.Def_PigeonholeSearch

namespace PigeonholeSearch

private abbrev Placement (n : ℕ) := Equiv.Perm (Fin (n+1))

private def critical {n : ℕ} (σ : Placement n) : Assignment n :=
  fun p h => decide (σ p = h.succ)

private def reporter {n : ℕ} : Clause n → Fin (n+1)
  | .row p => p
  | .collision p _ _ _ => p

private theorem critical_violation {n : ℕ} (σ : Placement n) (c : Clause n)
    (bad : c.violated (critical σ)) : σ (reporter c) = 0 := by
  cases c with
  | row p =>
    change σ p = 0
    cases place : σ p using Fin.cases with
    | zero => rfl
    | succ h => simpa [critical, place] using bad h
  | collision p q h ne =>
    have both : σ p = h.succ ∧ σ q = h.succ := by
      simpa [Clause.violated, critical] using bad
    exact False.elim (ne (σ.injective (both.1.trans both.2.symm)))

private def Agrees {n : ℕ} (s : Finset (Fin (n+1))) (σ τ : Placement n) :=
  ∀ i ∉ s, τ i = σ i

private theorem leaf_pos {n : ℕ} (t : Tree n) : 0 < t.leaves := by
  induction t <;> simp_all [Tree.leaves]

private theorem restricted_bound {n : ℕ} (t : Tree n) (s : Finset (Fin (n+1)))
    (σ : Placement n) (live : ∀ i ∉ s, σ i ≠ 0)
    (correct : ∀ τ : Placement n, Agrees s σ τ → τ (reporter (t.run (critical τ))) = 0) :
    2 ^ (s.card - 1) ≤ t.leaves := by
  classical
  induction t generalizing s σ with
  | leaf c =>
    let p := reporter c
    have base : σ p = 0 := correct σ (fun _ _ => rfl)
    have hp : p ∈ s := by by_contra hn; exact live p hn base
    by_cases small : s.card ≤ 1
    · simp [Tree.leaves, Nat.sub_eq_zero_of_le small]
    obtain ⟨q, hq, different⟩ := (Finset.one_lt_card_iff_nontrivial.mp (by omega : 1 < s.card)).exists_ne p
    let τ := (Equiv.swap p q).trans σ
    have agree : Agrees s σ τ := by
      intro i hi
      have a : i ≠ p := fun eq => hi (eq ▸ hp)
      have b : i ≠ q := fun eq => hi (eq ▸ hq)
      simp [τ, Equiv.swap_apply_of_ne_of_ne a b]
    have atq : σ q = 0 := by simpa [τ, p, Tree.run] using correct τ agree
    exact False.elim (different (σ.injective (atq.trans base.symm)))
  | query p h no yes ihNo ihYes =>
    let Good (τ : Placement n) := Agrees s σ τ
    have descend (τ : Placement n) (good : Good τ) :
        let r := τ.symm h.succ
        (∀ i ∉ s.erase r, τ i ≠ 0) ∧
        (∀ υ : Placement n, Agrees (s.erase r) τ υ →
          Good υ ∧ critical υ p h = critical τ p h) := by
      let r := τ.symm h.succ
      have placed : τ r = h.succ := τ.apply_symm_apply _
      constructor
      · intro i hi
        by_cases eq : i = r
        · simp [eq, placed]
        · have old : i ∉ s := fun mem => hi (Finset.mem_erase.mpr ⟨eq, mem⟩)
          rw [good i old]
          exact live i old
      · intro υ same
        have fixed : υ r = h.succ := (same r (Finset.notMem_erase _ _)).trans placed
        constructor
        · intro i hi
          exact (same i (fun m => hi (Finset.mem_of_mem_erase m))).trans (good i hi)
        · simp only [critical, ← placed, τ.injective.eq_iff]
          rw [placed, ← fixed]
          simp
    by_cases hasNo : ∃ τ : Placement n, Good τ ∧ critical τ p h = false
    · obtain ⟨τ₀, g₀, a₀⟩ := hasNo
      by_cases hasYes : ∃ τ : Placement n, Good τ ∧ critical τ p h = true
      · obtain ⟨τ₁, g₁, a₁⟩ := hasYes
        have subNo := ihNo (s.erase (τ₀.symm h.succ)) τ₀ (descend τ₀ g₀).1 (by
          intro υ agrees
          obtain ⟨g, a⟩ := (descend τ₀ g₀).2 υ agrees
          simpa [Tree.run, a.trans a₀] using correct υ g)
        have subYes := ihYes (s.erase (τ₁.symm h.succ)) τ₁ (descend τ₁ g₁).1 (by
          intro υ agrees
          obtain ⟨g, a⟩ := (descend τ₁ g₁).2 υ agrees
          simpa [Tree.run, a.trans a₁] using correct υ g)
        have residual (r : Fin (n+1)) : s.card - 2 ≤ (s.erase r).card - 1 := by
          by_cases mem : r ∈ s
          · rw [Finset.card_erase_of_mem mem]; omega
          · simp [Finset.erase_eq_of_notMem mem]; omega
        have a := (Nat.pow_le_pow_right (by decide : 0 < 2) (residual _)).trans subNo
        have b := (Nat.pow_le_pow_right (by decide : 0 < 2) (residual _)).trans subYes
        by_cases many : 2 ≤ s.card
        · rw [show s.card - 1 = s.card - 2 + 1 by omega, pow_succ, Tree.leaves]
          omega
        · rw [show s.card - 1 = 0 by omega, pow_zero]
          exact leaf_pos _
      · have lower := ihNo s σ live (by
          intro υ g
          have a : critical υ p h = false := by
            cases e : critical υ p h <;> simp_all [Good]
          simpa [Tree.run, a] using correct υ g)
        simp only [Tree.leaves]; omega
    · have lower := ihYes s σ live (by
        intro υ g
        have a : critical υ p h = true := by
          cases e : critical υ p h <;> simp_all [Good]
        simpa [Tree.run, a] using correct υ g)
      simp only [Tree.leaves]; omega

end PigeonholeSearch

open PigeonholeSearch

theorem solution (n : ℕ) (t : Tree n)
    (sound : ∀ x : Assignment n, (t.run x).violated x) : 2^n ≤ t.leaves := by
  simpa using restricted_bound t Finset.univ (Equiv.refl _) (by simp)
    (fun τ _ => critical_violation τ _ (sound _))

