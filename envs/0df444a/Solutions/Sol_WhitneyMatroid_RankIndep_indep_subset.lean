-- Prove2me | solution 1 for WhitneyMatroid.RankIndep.indep_subset
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T18:36:52.413356+00:00
-- url     : https://prove2.me/submissions/14426e34-8a5c-4fff-8e9d-5f98b385af7b

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates

open WhitneyMatroid.RankIndep

namespace WhitneyRI

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Rank systems: §§2–4 of Whitney -/

section rank

variable {r : Finset α → ℤ} (hr : IsRankSystem r)
include hr

lemma r_empty : r ∅ = 0 := hr.1

lemma r_insert_cases (N : Finset α) (e : α) : r (insert e N) = r N ∨ r (insert e N) = r N + 1 := by
  by_cases he : e ∈ N
  · left; rw [Finset.insert_eq_of_mem he]
  · exact hr.2.1 N e he

lemma r_mono_union (M D : Finset α) : r M ≤ r (M ∪ D) := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert d D _ ih =>
    rw [Finset.union_insert]
    rcases r_insert_cases hr (M ∪ D) d with h | h <;> omega

lemma r_mono {M N : Finset α} (h : M ⊆ N) : r M ≤ r N := by
  have := r_mono_union hr M N
  rwa [Finset.union_eq_right.2 h] at this

lemma r_nonneg (N : Finset α) : 0 ≤ r N := by
  have := r_mono hr (Finset.empty_subset N)
  rw [r_empty hr] at this
  exact this

lemma r_le_card (N : Finset α) : r N ≤ N.card := by
  induction N using Finset.induction_on with
  | empty => simp [r_empty hr]
  | insert e N he ih =>
    rw [Finset.card_insert_of_notMem he]
    rcases hr.2.1 N e he with h | h <;> push_cast <;> omega

/-- `r(A + D) ≤ r(A) + |D|`. -/
lemma r_le_add_card (A D : Finset α) : r (A ∪ D) ≤ r A + D.card := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert d D hd ih =>
    rw [Finset.union_insert, Finset.card_insert_of_notMem hd]
    rcases r_insert_cases hr (A ∪ D) d with h | h <;> push_cast <;> omega

lemma nullity_mono {A B : Finset α} (h : A ⊆ B) : nullity r A ≤ nullity r B := by
  unfold nullity
  have h1 := r_le_add_card hr A (B \ A)
  rw [Finset.union_sdiff_of_subset h] at h1
  have h2 : (B \ A).card + A.card = B.card := Finset.card_sdiff_add_card_eq_card h
  omega

lemma nullity_nonneg (A : Finset α) : 0 ≤ nullity r A := by
  unfold nullity; have := r_le_card hr A; omega

/-- Lemma 2: subsets of independent sets are independent. -/
lemma indep_sub {N N' : Finset α} (h : N ⊆ N') (hN' : indepOfRank r N') : indepOfRank r N := by
  have h1 := nullity_mono hr h
  have h2 := nullity_nonneg hr N
  unfold nullity at h1 h2
  unfold indepOfRank at hN' ⊢
  omega

/-- If `e` is dependent on `A`, it is dependent on every superset of `A` (via (R₃)). -/
lemma dep_lift {e : α} {A : Finset α} (hA : r (insert e A) = r A) (D : Finset α) :
    r (insert e (A ∪ D)) = r (A ∪ D) := by
  induction D using Finset.induction_on with
  | empty => simpa using hA
  | insert f D _ ih =>
    rw [Finset.union_insert]
    set A' := A ∪ D
    by_cases hf : f ∈ A'
    · rw [Finset.insert_eq_of_mem hf]; exact ih
    by_cases he : e ∈ A'
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem he)]
    by_cases hef : e = f
    · subst hef; rw [Finset.insert_idem]
    rcases hr.2.1 A' f hf with h | h
    · have h3 := hr.2.2 A' e f he hf ih h
      rw [h3, h]
    · have hef' : e ∉ insert f A' := by simp [hef, he]
      have h4 := hr.2.1 (insert f A') e hef'
      have h5 := r_insert_cases hr (insert e A') f
      rw [Finset.insert_comm] at h5
      omega

lemma dep_mono {e : α} {A B : Finset α} (hA : r (insert e A) = r A) (hAB : A ⊆ B) :
    r (insert e B) = r B := by
  have := dep_lift hr hA B
  rwa [Finset.union_eq_right.2 hAB] at this

/-- Lemmas 3 and 4: `Δ(B, e) ≤ Δ(A, e)` for `A ⊆ B`. -/
lemma delta_step (e : α) {A B : Finset α} (hAB : A ⊆ B) :
    r (insert e B) - r B ≤ r (insert e A) - r A := by
  rcases r_insert_cases hr A e with h | h
  · have := dep_mono hr h hAB; omega
  · rcases r_insert_cases hr B e with h' | h' <;> omega

/-- Theorem 3 in the form `Δ(B, D) ≤ Δ(A, D)` for `A ⊆ B`. -/
lemma delta_set_step {A B : Finset α} (hAB : A ⊆ B) (D : Finset α) :
    r (B ∪ D) - r B ≤ r (A ∪ D) - r A := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert d D _ ih =>
    rw [Finset.union_insert, Finset.union_insert]
    have := delta_step hr d (Finset.union_subset_union hAB (Finset.Subset.refl D))
    omega

/-- §4: (I₂) for the independent sets of a rank system. -/
lemma augment {N N' : Finset α} (hN : indepOfRank r N) (hN' : indepOfRank r N')
    (hc : N'.card = N.card + 1) : ∃ e ∈ N', e ∉ N ∧ indepOfRank r (insert e N) := by
  unfold indepOfRank at *
  by_contra hcon
  push Not at hcon
  -- every element of `N'` is dependent on `N`
  have hdep : ∀ e ∈ N', r (insert e N) = r N := by
    intro e he
    by_cases heN : e ∈ N
    · rw [Finset.insert_eq_of_mem heN]
    · have h1 := hcon e he heN
      rw [Finset.card_insert_of_notMem heN] at h1
      rcases hr.2.1 N e heN with h | h
      · exact h
      · exact absurd (by push_cast; omega) h1
  have hall : ∀ D : Finset α, D ⊆ N' → r (N ∪ D) = r N := by
    intro D
    induction D using Finset.induction_on with
    | empty => simp
    | insert d D _ ih =>
      intro hD
      rw [Finset.union_insert,
        dep_mono hr (hdep d (hD (Finset.mem_insert_self _ _))) Finset.subset_union_left]
      exact ih ((Finset.subset_insert _ _).trans hD)
  have h1 := hall N' (Finset.Subset.refl _)
  have h2 := r_mono hr (Finset.subset_union_right (s₁ := N) (s₂ := N'))
  rw [hc] at hN'
  push_cast at hN'
  omega

/-- A rank system has an independent subset of `N` of size `r(N)`. -/
lemma exists_basis (N : Finset α) : ∃ S ⊆ N, indepOfRank r S ∧ r S = r N := by
  induction N using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp [indepOfRank, r_empty hr], rfl⟩
  | insert e N he ih =>
    obtain ⟨S, hSN, hS, hSr⟩ := ih
    rcases hr.2.1 N e he with h | h
    · exact ⟨S, hSN.trans (Finset.subset_insert _ _), hS, by rw [h, hSr]⟩
    · have heS : e ∉ S := fun h' => he (hSN h')
      have h1 := delta_step hr e hSN
      have h2 := r_insert_cases hr S e
      refine ⟨insert e S, Finset.insert_subset_insert _ hSN, ?_, by omega⟩
      unfold indepOfRank at hS ⊢
      rw [Finset.card_insert_of_notMem heS]
      push_cast
      omega

end rank

/-! ### Rank of an independence system: §6 of Whitney -/

section indep

variable {I : Finset α → Prop}

lemma rankOfIndep_ge {S N : Finset α} (hS : S ⊆ N) (hI : I S) : (S.card : ℤ) ≤ rankOfIndep I N := by
  classical
  unfold rankOfIndep
  have : S.card ≤ (N.powerset.filter I).sup Finset.card :=
    Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hS, hI⟩)
  exact_mod_cast this

lemma rankOfIndep_attained (h0 : I ∅) (N : Finset α) :
    ∃ S ⊆ N, I S ∧ (S.card : ℤ) = rankOfIndep I N := by
  classical
  unfold rankOfIndep
  have hne : (N.powerset.filter I).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.empty_subset _), h0⟩⟩
  obtain ⟨S, hS, hSup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  obtain ⟨hSN, hSI⟩ := Finset.mem_filter.1 hS
  exact ⟨S, Finset.mem_powerset.1 hSN, hSI, by rw [hSup]⟩

/-- The general augmentation property from (I₁), (I₂). -/
lemma indep_augment (hI : IsIndepSystem I) {T S : Finset α} (hT : I T) (hS : I S)
    (hlt : T.card < S.card) : ∃ e ∈ S, e ∉ T ∧ I (insert e T) := by
  obtain ⟨S', hS'S, hS'c⟩ := Finset.exists_subset_card_eq (show T.card + 1 ≤ S.card by omega)
  obtain ⟨e, he, heT, hins⟩ := hI.2 T S' hT (hI.1 S' S hS'S hS) hS'c
  exact ⟨e, hS'S he, heT, hins⟩

lemma rankOfIndep_isRankSystem (hI : IsIndepSystem I) (h0 : I ∅) :
    IsRankSystem (rankOfIndep I) := by
  have mono : ∀ {A B : Finset α}, A ⊆ B → rankOfIndep I A ≤ rankOfIndep I B := by
    intro A B hAB
    obtain ⟨S, hSA, hS, hSc⟩ := rankOfIndep_attained h0 A
    rw [← hSc]
    exact rankOfIndep_ge (hSA.trans hAB) hS
  refine ⟨?_, ?_, ?_⟩
  · -- (R₁)
    obtain ⟨S, hS, -, hSc⟩ := rankOfIndep_attained h0 (∅ : Finset α)
    rw [Finset.subset_empty.1 hS] at hSc
    show rankOfIndep I ∅ = 0
    simpa using hSc.symm
  · -- (R₂)
    intro N e _
    have h1 := mono (Finset.subset_insert e N)
    obtain ⟨S, hSN, hS, hSc⟩ := rankOfIndep_attained h0 (insert e N)
    have h2 := rankOfIndep_ge (show S.erase e ⊆ N from fun x hx => by
      have := hSN (Finset.mem_of_mem_erase hx)
      rw [Finset.mem_insert] at this
      exact this.resolve_left (Finset.ne_of_mem_erase hx)) (hI.1 _ _ (Finset.erase_subset e S) hS)
    have h3 : S.card ≤ (S.erase e).card + 1 :=
      (Finset.card_le_card (Finset.insert_erase_subset e S)).trans
        (Finset.card_insert_le _ _)
    have h3' : (S.card : ℤ) ≤ (S.erase e).card + 1 := by exact_mod_cast h3
    omega
  · -- (R₃)
    intro N e₁ e₂ _ _ h1 h2
    have hm := (mono (Finset.subset_insert e₂ N)).trans
      (mono (Finset.subset_insert e₁ (insert e₂ N)))
    obtain ⟨S, hSN, hS, hSc⟩ := rankOfIndep_attained h0 (insert e₁ (insert e₂ N))
    obtain ⟨T, hTN, hT, hTc⟩ := rankOfIndep_attained h0 N
    by_contra hne
    have hlt : T.card < S.card := by
      have : (T.card : ℤ) < S.card := by omega
      exact_mod_cast this
    obtain ⟨e, heS, heT, hins⟩ := indep_augment hI hT hS hlt
    have hc : ((insert e T).card : ℤ) = T.card + 1 := by
      rw [Finset.card_insert_of_notMem heT]; push_cast; ring
    have he := hSN heS
    simp only [Finset.mem_insert] at he
    rcases he with rfl | rfl | heN
    · have := rankOfIndep_ge (Finset.insert_subset_insert e hTN) hins
      omega
    · have := rankOfIndep_ge (Finset.insert_subset_insert e hTN) hins
      omega
    · have := rankOfIndep_ge (Finset.insert_subset heN hTN) hins
      omega

lemma indepOfRank_rankOfIndep (h0 : I ∅) : indepOfRank (rankOfIndep I) = I := by
  funext N
  apply propext
  unfold indepOfRank
  obtain ⟨S, hSN, hS, hSc⟩ := rankOfIndep_attained h0 N
  constructor
  · intro h
    have hcard : N.card ≤ S.card := by
      have : (N.card : ℤ) ≤ S.card := by omega
      exact_mod_cast this
    rw [← Finset.eq_of_subset_of_card_le hSN hcard]
    exact hS
  · intro hN
    have h1 := rankOfIndep_ge (Finset.Subset.refl N) hN
    have h2 : (S.card : ℤ) ≤ N.card := by exact_mod_cast Finset.card_le_card hSN
    omega

end indep

lemma rankOfIndep_indepOfRank {r : Finset α → ℤ} (hr : IsRankSystem r) :
    rankOfIndep (indepOfRank r) = r := by
  funext N
  have h0 : indepOfRank r ∅ := by simp [indepOfRank, r_empty hr]
  obtain ⟨S, hSN, hS, hSc⟩ := rankOfIndep_attained h0 N
  obtain ⟨B, hBN, hB, hBr⟩ := exists_basis hr N
  have h1 := rankOfIndep_ge hBN hB
  unfold indepOfRank at hS hB
  have h2 := r_mono hr hSN
  omega

end WhitneyRI

open WhitneyRI in
theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) :
    ∀ N N' : Finset α, N ⊆ N' → indepOfRank r N' → indepOfRank r N :=
  fun _ _ h hN => indep_sub hr h hN
