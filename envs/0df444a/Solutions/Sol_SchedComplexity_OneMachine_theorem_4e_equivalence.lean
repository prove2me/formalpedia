-- Prove2me | solution 1 for SchedComplexity.OneMachine.theorem_4e_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:09:03.872198+00:00
-- url     : https://prove2.me/submissions/9c853eb2-6496-4639-be18-119002d5f976

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Constructions



namespace SchedComplexity.OneMachine
open Finset

def spos {t : ℕ} (p : Fin t → ℕ) (T : Finset (Fin t)) (j : Fin t) : ℕ :=
  ∑ k ∈ T.filter (· < j), p k

lemma spos_add_le {t : ℕ} (p : Fin t → ℕ) (T : Finset (Fin t)) {j : Fin t} (hj : j ∈ T) :
    spos p T j + p j ≤ ∑ k ∈ T, p k := by
  unfold spos
  have : j ∉ T.filter (· < j) := by simp
  rw [add_comm, ← Finset.sum_insert this]
  apply Finset.sum_le_sum_of_subset
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact hj
  · exact (Finset.mem_filter.1 hx).1

lemma spos_step {t : ℕ} (p : Fin t → ℕ) (T : Finset (Fin t)) {j k : Fin t} (hjk : j < k)
    (hj : j ∈ T) : spos p T j + p j ≤ spos p T k := by
  unfold spos
  have : j ∉ T.filter (· < j) := by simp
  rw [add_comm, ← Finset.sum_insert this]
  apply Finset.sum_le_sum_of_subset
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · simp [hj, hjk]
  · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 hjk⟩

lemma ico_fdisj {x p y q : ℕ} (h : x + p ≤ y ∨ y + q ≤ x) :
    Disjoint (Finset.Ico x (x+p)) (Finset.Ico y (y+q)) := by
  rw [Finset.disjoint_left]; intro z h1 h2
  simp only [Finset.mem_Ico] at h1 h2; omega

lemma ico_sdisj {x p y q : ℕ} (h : x + p ≤ y ∨ y + q ≤ x) :
    Disjoint (Set.Ico x (x+p)) (Set.Ico y (y+q)) := by
  rw [Set.disjoint_left]; intro z h1 h2
  simp only [Set.mem_Ico] at h1 h2; omega

lemma sep_of_sdisj {x p y q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (h : Disjoint (Set.Ico x (x+p)) (Set.Ico y (y+q))) : x + p ≤ y ∨ y + q ≤ x := by
  by_contra hc
  push Not at hc
  rw [Set.disjoint_left] at h
  rcases le_total x y with hxy | hxy
  · have h1 : y ∈ Set.Ico x (x+p) := by simp only [Set.mem_Ico]; omega
    have h2 : y ∈ Set.Ico y (y+q) := by simp only [Set.mem_Ico]; omega
    exact h h1 h2
  · have h1 : x ∈ Set.Ico x (x+p) := by simp only [Set.mem_Ico]; omega
    have h2 : x ∈ Set.Ico y (y+q) := by simp only [Set.mem_Ico]; omega
    exact h h1 h2

lemma sum_get_eq (a : List ℕ) : ∑ j : Fin a.length, a.get j = a.sum := by
  simpa using (List.sum_ofFn (f := a.get))

lemma sum_compl_get (a : List ℕ) (S : Finset (Fin a.length)) :
    ∑ j ∈ Sᶜ, a.get j + ∑ j ∈ S, a.get j = a.sum := by
  rw [Finset.sum_compl_add_sum]; exact sum_get_eq a

def eB (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (j : Fin a.length) : ℕ :=
  if j ∈ S then spos a.get S j else b + spos a.get Sᶜ j

lemma eB_sep (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    (j k : Fin a.length) (hjk : j < k) :
    eB a b S j + a.get j ≤ eB a b S k ∨ eB a b S k + a.get k ≤ eB a b S j := by
  unfold eB
  by_cases hj : j ∈ S <;> by_cases hk : k ∈ S
  · simp only [hj, hk, if_true]; left; exact spos_step _ _ hjk hj
  · simp only [hj, hk, if_true, if_false]
    have := spos_add_le a.get S hj
    left; omega
  · simp only [hj, hk, if_true, if_false]
    have := spos_add_le a.get S hk
    right; omega
  · simp only [hj, hk, if_false]
    have := spos_step a.get Sᶜ hjk (by simpa using hj)
    left; omega

lemma e_forward (a : List ℕ) (b : ℕ) (hbA : b < a.sum) (S : Finset (Fin a.length))
    (hS : ∑ j ∈ S, a.get j = b) :
    (instE a b).IsFeasible (eB a b S) ∧ (instE a b).sumWU (eB a b S) ≤ yE a b := by
  have hc := sum_compl_get a S
  constructor
  · constructor
    · intro j; simp [instE]
    · intro j k hjk
      simp only [instE]
      apply ico_sdisj
      rcases lt_or_gt_of_ne hjk with h | h
      · exact eB_sep a b S hS j k h
      · exact (eB_sep a b S hS k j h).symm
  · unfold Instance.sumWU yE
    have h1 : ∀ j : Fin a.length, (instE a b).w j * (instE a b).U (eB a b S) j
        ≤ if j ∈ Sᶜ then a.get j else 0 := by
      intro j
      have hw : (instE a b).w j = a.get j := rfl
      rw [hw]
      by_cases hj : j ∈ S
      · have hjc : j ∉ Sᶜ := by simpa using hj
        rw [if_neg hjc]
        have : (instE a b).C (eB a b S) j ≤ (instE a b).d j := by
          have := spos_add_le a.get S hj
          show eB a b S j + a.get j ≤ b
          unfold eB; simp only [hj, if_true]; omega
        have hU : (instE a b).U (eB a b S) j = 0 := by
          unfold Instance.U; rw [if_pos this]
        rw [hU]; simp
      · have hjc : j ∈ Sᶜ := by simpa using hj
        rw [if_pos hjc]
        have : (instE a b).U (eB a b S) j ≤ 1 := by
          unfold Instance.U; split_ifs <;> omega
        calc a.get j * (instE a b).U (eB a b S) j ≤ a.get j * 1 := Nat.mul_le_mul_left _ this
          _ = a.get j := by simp
    have h2 := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin a.length))) => h1 j)
    have h3 : ∑ j : Fin a.length, (if j ∈ Sᶜ then a.get j else 0) = ∑ j ∈ Sᶜ, a.get j := by
      rw [← Finset.sum_filter]; congr 1; ext x; simp
    have : (instE a b).n = a.length := rfl
    refine le_trans h2 ?_
    rw [h3]; omega

lemma e_backward (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hbA : b < a.sum)
    (B : Fin a.length → ℕ) (hf : (instE a b).IsFeasible B)
    (hl : (instE a b).sumWU B ≤ yE a b) : KnapsackYes a b := by
  have hpos : ∀ j : Fin a.length, 0 < a.get j := fun j => ha _ (List.get_mem _ _)
  have hsep : ∀ j k : Fin a.length, j ≠ k →
      B j + a.get j ≤ B k ∨ B k + a.get k ≤ B j := by
    intro j k hjk
    have := hf.2 j k hjk
    exact sep_of_sdisj (hpos j) (hpos k) this
  let S : Finset (Fin a.length) := Finset.univ.filter (fun j => B j + a.get j ≤ b)
  refine ⟨S, ?_⟩
  let I : Fin a.length → Finset ℕ := fun j => Finset.Ico (B j) (B j + a.get j)
  have hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (I x) (I y) :=
    fun x _ y _ hxy => ico_fdisj (hsep x y hxy)
  have hcard : (S.biUnion I).card = ∑ j ∈ S, a.get j := by
    rw [Finset.card_biUnion hdisj]
    simp only [I, Nat.card_Ico, Nat.add_sub_cancel_left]
  have hsub : S.biUnion I ⊆ Finset.range b := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨j, hj, hz⟩ := hz
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [I, Finset.mem_Ico] at hz
    simp only [Finset.mem_range]; omega
  have hle : ∑ j ∈ S, a.get j ≤ b := by
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega
  -- late part
  have hU : (instE a b).sumWU B = ∑ j ∈ Sᶜ, a.get j := by
    unfold Instance.sumWU
    show ∑ j : Fin a.length, (instE a b).w j * (instE a b).U B j = _
    rw [← Finset.sum_compl_add_sum S]
    have h1 : ∑ j ∈ S, (instE a b).w j * (instE a b).U B j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have : (instE a b).C B j ≤ (instE a b).d j := hj
      have hU : (instE a b).U B j = 0 := by unfold Instance.U; rw [if_pos this]
      rw [hU]; simp
    rw [h1, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : ¬ (B j + a.get j ≤ b) := by simpa [S] using hj
    have : ¬ (instE a b).C B j ≤ (instE a b).d j := hj'
    have hU : (instE a b).U B j = 1 := by unfold Instance.U; rw [if_neg this]
    rw [hU]; show a.get j * 1 = a.get j; simp
  have hc := sum_compl_get a S
  unfold yE at hl
  omega

theorem e_core (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instE a b).IsFeasible B ∧ (instE a b).sumWU B ≤ yE a b := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨_, e_forward a b hbA S hS⟩
  · rintro ⟨B, hf, hl⟩
    exact e_backward a b ha hbA B hf hl

end SchedComplexity.OneMachine

open SchedComplexity.OneMachine


theorem solution (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instE a b).IsFeasible B ∧ (instE a b).sumWU B ≤ yE a b := by
  exact e_core a b ha hb hbA
