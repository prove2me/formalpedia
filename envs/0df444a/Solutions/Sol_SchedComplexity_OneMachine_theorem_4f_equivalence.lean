-- Prove2me | solution 1 for SchedComplexity.OneMachine.theorem_4f_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:07:49.888193+00:00
-- url     : https://prove2.me/submissions/d7156328-5cec-4697-8c01-eeaf46d1d1a0

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

/-- start times of the forward schedule for (c) -/
def cfB (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) : Fin (a.length + 1) → ℕ :=
  fun i => Fin.lastCases (motive := fun _ => ℕ) b
    (fun j => if j ∈ S then spos a.get S j else b + 1 + spos a.get Sᶜ j) i

lemma cfB_last (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) : cfB a b S (Fin.last _) = b := by
  simp [cfB]

lemma cfB_cast (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (j : Fin a.length) :
    cfB a b S j.castSucc = if j ∈ S then spos a.get S j else b + 1 + spos a.get Sᶜ j := by
  simp [cfB]

lemma cfB_sep (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    (j k : Fin a.length) (hjk : j < k) :
    cfB a b S j.castSucc + a.get j ≤ cfB a b S k.castSucc ∨
      cfB a b S k.castSucc + a.get k ≤ cfB a b S j.castSucc := by
  rw [cfB_cast, cfB_cast]
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

lemma cfB_le (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    (j : Fin a.length) :
    cfB a b S j.castSucc + a.get j ≤ (if j ∈ S then b else a.sum + 1) := by
  rw [cfB_cast]
  have hc := sum_compl_get a S
  by_cases hj : j ∈ S
  · simp only [hj, if_true]; have := spos_add_le a.get S hj; omega
  · simp only [hj, if_false]
    have := spos_add_le a.get Sᶜ (by simpa using hj)
    omega

lemma cfB_side (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    (k : Fin a.length) :
    cfB a b S k.castSucc + a.get k ≤ b ∨ b + 1 ≤ cfB a b S k.castSucc := by
  have h1 := cfB_le a b S hS k
  by_cases hk : k ∈ S
  · simp only [hk, if_true] at h1; left; exact h1
  · right; rw [cfB_cast]; simp only [hk, if_false]; omega

lemma cf_forward (a : List ℕ) (b : ℕ) (hbA : b < a.sum) (S : Finset (Fin a.length))
    (hS : ∑ j ∈ S, a.get j = b) :
    (instCF a b).IsFeasible (cfB a b S) ∧ ∀ j, (instCF a b).lateness (cfB a b S) j ≤ 0 := by
  have hc := sum_compl_get a S
  constructor
  · constructor
    · intro j
      induction j using Fin.lastCases with
      | last => simp [instCF, cfB_last]
      | cast j => simp [instCF]
    · intro j k hjk
      induction j using Fin.lastCases with
      | last =>
        induction k using Fin.lastCases with
        | last => exact absurd rfl hjk
        | cast k =>
          simp only [instCF, Fin.lastCases_last, Fin.lastCases_castSucc, cfB_last]
          apply ico_sdisj
          have := cfB_side a b S hS k
          omega
      | cast j =>
        induction k using Fin.lastCases with
        | last =>
          simp only [instCF, Fin.lastCases_last, Fin.lastCases_castSucc, cfB_last]
          apply ico_sdisj
          have := cfB_side a b S hS j
          omega
        | cast k =>
          have hne : j ≠ k := fun h => hjk (by rw [h])
          simp only [instCF, Fin.lastCases_castSucc]
          apply ico_sdisj
          rcases lt_or_gt_of_ne hne with h | h
          · exact cfB_sep a b S hS j k h
          · exact (cfB_sep a b S hS k j h).symm
  · intro j
    induction j using Fin.lastCases with
    | last => simp [Instance.lateness, Instance.C, instCF, cfB_last]
    | cast j =>
      have h1 := cfB_le a b S hS j
      simp only [Instance.lateness, Instance.C, instCF, Fin.lastCases_castSucc]
      have : (if j ∈ S then b else a.sum + 1) ≤ a.sum + 1 := by split_ifs <;> omega
      have h3 : cfB a b S j.castSucc + a.get j ≤ a.sum + 1 := le_trans h1 this
      omega

lemma cf_backward (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hbA : b < a.sum)
    (B : Fin (a.length + 1) → ℕ) (hf : (instCF a b).IsFeasible B)
    (hl : ∀ j, (instCF a b).lateness B j ≤ 0) : KnapsackYes a b := by
  have hpos : ∀ j : Fin a.length, 0 < a.get j := fun j => ha _ (List.get_mem _ _)
  have hlast := hl (Fin.last _)
  have hr := hf.1 (Fin.last _)
  simp only [Instance.lateness, Instance.C, instCF, Fin.lastCases_last] at hlast hr
  have hBl : B (Fin.last _) = b := by omega
  have hc : ∀ j : Fin a.length, B j.castSucc + a.get j ≤ a.sum + 1 := by
    intro j
    have := hl j.castSucc
    simp only [Instance.lateness, Instance.C, instCF, Fin.lastCases_castSucc] at this
    omega
  have hsepl : ∀ j : Fin a.length, B j.castSucc + a.get j ≤ b ∨ b + 1 ≤ B j.castSucc := by
    intro j
    have := hf.2 j.castSucc (Fin.last _) (Fin.castSucc_lt_last j).ne
    simp only [instCF, Fin.lastCases_last, Fin.lastCases_castSucc] at this
    have := sep_of_sdisj (hpos j) (by norm_num) this
    omega
  have hsep : ∀ j k : Fin a.length, j ≠ k →
      B j.castSucc + a.get j ≤ B k.castSucc ∨ B k.castSucc + a.get k ≤ B j.castSucc := by
    intro j k hjk
    have := hf.2 j.castSucc k.castSucc (fun h => hjk (Fin.castSucc_injective _ h))
    simp only [instCF, Fin.lastCases_castSucc] at this
    exact sep_of_sdisj (hpos j) (hpos k) this
  let I : Fin a.length → Finset ℕ := fun j => Finset.Ico (B j.castSucc) (B j.castSucc + a.get j)
  have hdisj : ∀ x ∈ (Finset.univ : Finset (Fin a.length)), ∀ y ∈ (Finset.univ : Finset (Fin a.length)),
      x ≠ y → Disjoint (I x) (I y) := fun x _ y _ hxy => ico_fdisj (hsep x y hxy)
  have hcardU : (Finset.univ.biUnion I).card = a.sum := by
    rw [Finset.card_biUnion hdisj]
    simp only [I, Nat.card_Ico, Nat.add_sub_cancel_left]
    exact sum_get_eq a
  have hsub : Finset.univ.biUnion I ⊆ (Finset.range (a.sum + 1)).erase b := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨j, -, hz⟩ := hz
    simp only [I, Finset.mem_Ico] at hz
    simp only [Finset.mem_erase, Finset.mem_range]
    have := hc j
    have := hsepl j
    omega
  have hcardE : ((Finset.range (a.sum + 1)).erase b).card = a.sum := by
    rw [Finset.card_erase_of_mem (by simp; omega)]; simp
  have heq : Finset.univ.biUnion I = (Finset.range (a.sum + 1)).erase b :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardU, hcardE])
  refine ⟨Finset.univ.filter (fun j => B j.castSucc < b), ?_⟩
  have hdisj2 : ∀ x ∈ (Finset.univ.filter (fun j : Fin a.length => B j.castSucc < b)),
      ∀ y ∈ (Finset.univ.filter (fun j : Fin a.length => B j.castSucc < b)),
      x ≠ y → Disjoint (I x) (I y) := fun x _ y _ hxy => hdisj x (by simp) y (by simp) hxy
  have h3 : (Finset.univ.filter (fun j : Fin a.length => B j.castSucc < b)).biUnion I
      = Finset.range b := by
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hz⟩
      simp only [I, Finset.mem_Ico] at hz
      have := hsepl j
      omega
    · intro hz
      have hmem : z ∈ Finset.univ.biUnion I := by
        rw [heq]; simp only [Finset.mem_erase, Finset.mem_range]; omega
      rw [Finset.mem_biUnion] at hmem
      obtain ⟨j, -, hj⟩ := hmem
      simp only [I, Finset.mem_Ico] at hj
      exact ⟨j, by omega, by simp only [I, Finset.mem_Ico]; exact hj⟩
  have h4 := congrArg Finset.card h3
  rw [Finset.card_biUnion hdisj2] at h4
  simp only [I, Nat.card_Ico, Nat.add_sub_cancel_left, Finset.card_range] at h4
  exact h4

theorem cf_core_c (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instCF a b).IsFeasible B ∧ ∀ j, (instCF a b).lateness B j ≤ 0 := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨_, cf_forward a b hbA S hS⟩
  · rintro ⟨B, hf, hl⟩
    exact cf_backward a b ha hbA B hf hl

theorem cf_core_f (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instCF a b).IsFeasible B ∧ (instCF a b).sumWU B ≤ 0 := by
  rw [cf_core_c a b ha hb hbA]
  apply exists_congr; intro B
  apply and_congr_right; intro _
  have key : (instCF a b).sumWU B ≤ 0 ↔ ∀ j, (instCF a b).lateness B j ≤ 0 := by
    unfold Instance.sumWU
    rw [Nat.le_zero, Finset.sum_eq_zero_iff]
    apply forall_congr'; intro j
    simp only [Finset.mem_univ, true_implies, Instance.lateness, Instance.U]
    have : (instCF a b).w j = 1 := rfl
    rw [this]
    rw [one_mul]
    by_cases h : (instCF a b).C B j ≤ (instCF a b).d j
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  exact key.symm

end SchedComplexity.OneMachine

open SchedComplexity.OneMachine


theorem solution (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instCF a b).IsFeasible B ∧ (instCF a b).sumWU B ≤ 0 := by
  exact cf_core_f a b ha hb hbA
