-- Prove2me | solution 1 for StochIneqPO.Comparison.theorem1_vi_imp_ii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T18:24:52.519212+00:00
-- url     : https://prove2.me/submissions/13ca40bf-072f-4670-ac1c-9a90d061961f

import Mathlib

set_option autoImplicit false

section PartA
open Finset

namespace StrassenA

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  (R : ι → κ → Prop) [DecidableRel R]

/-- Neighbourhood of `A` inside `J`. -/
def nbr (J : Finset κ) (A : Finset ι) : Finset κ := J.filter (fun j => ∃ i ∈ A, R i j)

/-- A transport plan for the instance `(I, J, μ, ν)`. -/
def Plan (I : Finset ι) (J : Finset κ) (μ : ι → ℝ) (ν : κ → ℝ) (π : ι → κ → ℝ) : Prop :=
  (∀ i j, 0 ≤ π i j) ∧ (∀ i j, π i j ≠ 0 → i ∈ I ∧ j ∈ J ∧ R i j) ∧
  (∀ i ∈ I, ∑ j, π i j = μ i) ∧ (∀ j ∈ J, ∑ i, π i j ≤ ν j)

/-- Nonnegativity plus the weighted Hall condition. -/
def Hall (I : Finset ι) (J : Finset κ) (μ : ι → ℝ) (ν : κ → ℝ) : Prop :=
  (∀ i ∈ I, 0 ≤ μ i) ∧ (∀ j ∈ J, 0 ≤ ν j) ∧ ∀ A ⊆ I, ∑ i ∈ A, μ i ≤ ∑ j ∈ nbr R J A, ν j

variable {R}

lemma row_zero {I : Finset ι} {J : Finset κ} {μ : ι → ℝ} {ν : κ → ℝ} {π : ι → κ → ℝ}
    (hπ : Plan R I J μ ν π) {i : ι} (hi : i ∉ I) : ∑ j, π i j = 0 :=
  sum_eq_zero fun j _ => by
    by_contra h
    exact hi (hπ.2.1 i j h).1

lemma col_zero {I : Finset ι} {J : Finset κ} {μ : ι → ℝ} {ν : κ → ℝ} {π : ι → κ → ℝ}
    (hπ : Plan R I J μ ν π) {j : κ} (hj : j ∉ J) : ∑ i, π i j = 0 :=
  sum_eq_zero fun i _ => by
    by_contra h
    exact hj (hπ.2.1 i j h).2.1

lemma plan_zero {I : Finset ι} {J : Finset κ} {μ : ι → ℝ} {ν : κ → ℝ} (hI : I = ∅)
    (hν : ∀ j ∈ J, 0 ≤ ν j) : Plan R I J μ ν (fun _ _ => 0) := by
  refine ⟨fun _ _ => le_rfl, fun _ _ h => absurd rfl h, ?_, ?_⟩
  · intro i hi; simp [hI] at hi
  · intro j hj; simpa using hν j hj

lemma nbr_subset (J : Finset κ) (A : Finset ι) : nbr R J A ⊆ J := filter_subset _ _

/-- Split along a tight proper nonempty set. -/
lemma split (I : Finset ι) (J : Finset κ) (μ : ι → ℝ) (ν : κ → ℝ) (hH : Hall R I J μ ν)
    (A : Finset ι) (hA : A ⊆ I) (hAne : A.Nonempty) (hAI : A ≠ I)
    (htight : ∑ i ∈ A, μ i = ∑ j ∈ nbr R J A, ν j)
    (IH : ∀ (I' : Finset ι) (J' : Finset κ) (μ' : ι → ℝ) (ν' : κ → ℝ),
      I'.card + J'.card < I.card + J.card → Hall R I' J' μ' ν' →
        ∃ π, Plan R I' J' μ' ν' π) :
    ∃ π, Plan R I J μ ν π := by
  have hcA : A.card < I.card := card_lt_card (ssubset_of_subset_of_ne hA hAI)
  have hcN : (nbr R J A).card ≤ J.card := card_le_card (nbr_subset J A)
  have hcIA : (I \ A).card < I.card := card_lt_card (sdiff_ssubset hA hAne)
  have hcJN : (J \ nbr R J A).card ≤ J.card := card_le_card sdiff_subset
  -- first piece
  have H1 : Hall R A (nbr R J A) μ ν := by
    refine ⟨fun i hi => hH.1 i (hA hi), fun j hj => hH.2.1 j (nbr_subset J A hj), ?_⟩
    intro A' hA'
    have : nbr R (nbr R J A) A' = nbr R J A' := by
      ext j
      simp only [nbr, mem_filter]
      constructor
      · rintro ⟨⟨hj, -⟩, h⟩; exact ⟨hj, h⟩
      · rintro ⟨hj, i, hi, hr⟩; exact ⟨⟨hj, i, hA' hi, hr⟩, i, hi, hr⟩
    rw [this]
    exact hH.2.2 A' (hA'.trans hA)
  -- second piece
  have H2 : Hall R (I \ A) (J \ nbr R J A) μ ν := by
    refine ⟨fun i hi => hH.1 i (sdiff_subset hi), fun j hj => hH.2.1 j (sdiff_subset hj), ?_⟩
    intro A' hA'
    have hdisj : Disjoint A A' := by
      rw [disjoint_left]; intro i hi hi'; exact (mem_sdiff.mp (hA' hi')).2 hi
    have hU : A ∪ A' ⊆ I := union_subset hA (hA'.trans sdiff_subset)
    have hnb : nbr R J (A ∪ A') = nbr R J A ∪ nbr R (J \ nbr R J A) A' := by
      ext j
      simp only [nbr, mem_filter, mem_union, mem_sdiff]
      by_cases h : ∃ i ∈ A, R i j
      · constructor
        · rintro ⟨hj, -⟩; exact Or.inl ⟨hj, h⟩
        · rintro (⟨hj, i, hi, hr⟩ | ⟨⟨hj, -⟩, i, hi, hr⟩)
          · exact ⟨hj, i, Or.inl hi, hr⟩
          · exact ⟨hj, i, Or.inr hi, hr⟩
      · constructor
        · rintro ⟨hj, i, hi, hr⟩
          rcases hi with hi | hi
          · exact absurd ⟨i, hi, hr⟩ h
          · exact Or.inr ⟨⟨hj, fun hh => h hh.2⟩, i, hi, hr⟩
        · rintro (⟨hj, i, hi, hr⟩ | ⟨⟨hj, -⟩, i, hi, hr⟩)
          · exact ⟨hj, i, Or.inl hi, hr⟩
          · exact ⟨hj, i, Or.inr hi, hr⟩
    have hdisj2 : Disjoint (nbr R J A) (nbr R (J \ nbr R J A) A') := by
      rw [disjoint_left]; intro j hj hj'
      simp only [nbr, mem_filter, mem_sdiff] at hj'
      exact hj'.1.2 (by simpa only [nbr, mem_filter] using hj)
    have h1 := hH.2.2 _ hU
    rw [hnb, sum_union hdisj2, sum_union hdisj] at h1
    linarith
  obtain ⟨π1, hπ1⟩ := IH _ _ μ ν (by omega) H1
  obtain ⟨π2, hπ2⟩ := IH _ _ μ ν (by omega) H2
  refine ⟨fun i j => π1 i j + π2 i j, fun i j => add_nonneg (hπ1.1 i j) (hπ2.1 i j), ?_, ?_, ?_⟩
  · intro i j h
    by_cases h1 : π1 i j = 0
    · have h2 : π2 i j ≠ 0 := by intro h2; exact h (by simp [h1, h2])
      obtain ⟨a, b, c⟩ := hπ2.2.1 i j h2
      exact ⟨sdiff_subset a, sdiff_subset b, c⟩
    · obtain ⟨a, b, c⟩ := hπ1.2.1 i j h1
      exact ⟨hA a, nbr_subset J A b, c⟩
  · intro i hi
    rw [sum_add_distrib]
    by_cases hiA : i ∈ A
    · rw [hπ1.2.2.1 i hiA, row_zero hπ2 (fun h => (mem_sdiff.mp h).2 hiA), add_zero]
    · rw [row_zero hπ1 hiA, hπ2.2.2.1 i (mem_sdiff.mpr ⟨hi, hiA⟩), zero_add]
  · intro j hj
    rw [sum_add_distrib]
    by_cases hjN : j ∈ nbr R J A
    · rw [col_zero hπ2 (fun h => (mem_sdiff.mp h).2 hjN), add_zero]
      exact hπ1.2.2.2 j hjN
    · rw [col_zero hπ1 hjN, zero_add]
      exact hπ2.2.2.2 j (mem_sdiff.mpr ⟨hj, hjN⟩)

/-- Push mass `t` on the edge `(i0, j0)`. -/
lemma plan_push {I : Finset ι} {J : Finset κ} {μ : ι → ℝ} {ν : κ → ℝ} {π : ι → κ → ℝ}
    {i0 : ι} {j0 : κ} {t : ℝ} (ht : 0 ≤ t) (hi0 : i0 ∈ I) (hj0 : j0 ∈ J) (hr : R i0 j0)
    (hπ : Plan R I J (fun i => μ i - if i = i0 then t else 0)
      (fun j => ν j - if j = j0 then t else 0) π) :
    Plan R I J μ ν (fun i j => π i j + if i = i0 ∧ j = j0 then t else 0) := by
  refine ⟨fun i j => add_nonneg (hπ.1 i j) (by split_ifs <;> simp [ht]), ?_, ?_, ?_⟩
  · intro i j h
    by_cases h0 : i = i0 ∧ j = j0
    · obtain ⟨rfl, rfl⟩ := h0; exact ⟨hi0, hj0, hr⟩
    · have : π i j ≠ 0 := by intro h'; exact h (by simp [h', h0])
      exact hπ.2.1 i j this
  · intro i hi
    rw [sum_add_distrib, hπ.2.2.1 i hi]
    by_cases h0 : i = i0
    · subst h0; simp
    · simp [h0]
  · intro j hj
    rw [sum_add_distrib]
    have := hπ.2.2.2 j hj
    by_cases h0 : j = j0
    · subst h0; simp at this ⊢; linarith
    · simp [h0] at this ⊢; linarith

theorem main (n : ℕ) : ∀ (I : Finset ι) (J : Finset κ) (μ : ι → ℝ) (ν : κ → ℝ),
    I.card + J.card = n → Hall R I J μ ν → ∃ π, Plan R I J μ ν π := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro I J μ ν hn hH
  have IH : ∀ (I' : Finset ι) (J' : Finset κ) (μ' : ι → ℝ) (ν' : κ → ℝ),
      I'.card + J'.card < I.card + J.card → Hall R I' J' μ' ν' →
        ∃ π, Plan R I' J' μ' ν' π :=
    fun I' J' μ' ν' hlt h => ih _ (hn ▸ hlt) I' J' μ' ν' rfl h
  by_cases ht : ∃ A ⊆ I, A.Nonempty ∧ A ≠ I ∧ ∑ i ∈ A, μ i = ∑ j ∈ nbr R J A, ν j
  · obtain ⟨A, hA, hne, hAI, htt⟩ := ht
    exact split I J μ ν hH A hA hne hAI htt IH
  push_neg at ht
  rcases I.eq_empty_or_nonempty with hI | ⟨i0, hi0⟩
  · exact ⟨_, plan_zero hI hH.2.1⟩
  -- dropping a row of zero supply
  have drop : ∀ (μ' : ι → ℝ) (ν' : κ → ℝ), Hall R I J μ' ν' → μ' i0 = 0 →
      ∃ π, Plan R I J μ' ν' π := by
    intro μ' ν' hH' h0
    have hH'' : Hall R (I.erase i0) J μ' ν' :=
      ⟨fun i hi => hH'.1 i (mem_of_mem_erase hi), hH'.2.1,
        fun A hA => hH'.2.2 A (hA.trans (erase_subset _ _))⟩
    obtain ⟨π, hπ⟩ := IH _ _ μ' ν' (by have := card_erase_lt_of_mem hi0; omega) hH''
    refine ⟨π, hπ.1, fun i j h => ?_, fun i hi => ?_, fun j hj => hπ.2.2.2 j hj⟩
    · obtain ⟨a, b, c⟩ := hπ.2.1 i j h; exact ⟨mem_of_mem_erase a, b, c⟩
    · by_cases hii : i = i0
      · subst hii; rw [row_zero hπ (fun h => (mem_erase.mp h).1 rfl), h0]
      · exact hπ.2.2.1 i (mem_erase.mpr ⟨hii, hi⟩)
  by_cases hμ0 : μ i0 = 0
  · exact drop μ ν hH hμ0
  have hμpos : 0 < μ i0 := lt_of_le_of_ne (hH.1 i0 hi0) (Ne.symm hμ0)
  -- an edge out of i0 with positive capacity
  obtain ⟨j0, hj0N, hνpos⟩ : ∃ j0 ∈ nbr R J {i0}, 0 < ν j0 := by
    by_contra hc
    push_neg at hc
    have h1 := hH.2.2 {i0} (singleton_subset_iff.mpr hi0)
    have h2 : ∑ j ∈ nbr R J {i0}, ν j ≤ 0 := sum_nonpos hc
    rw [sum_singleton] at h1
    linarith
  have hj0 : j0 ∈ J := nbr_subset J {i0} hj0N
  have hr0 : R i0 j0 := by
    simp only [nbr, mem_filter, mem_singleton, exists_eq_left] at hj0N
    exact hj0N.2
  -- slack bound over the sets that the push affects
  set S := (I.erase i0).powerset.filter (fun A => j0 ∈ nbr R J A) with hS
  have hSmem : ∀ A ∈ S, A ⊆ I ∧ i0 ∉ A ∧ A.Nonempty ∧ A ≠ I ∧ j0 ∈ nbr R J A := by
    intro A hAS
    rw [hS, mem_filter, mem_powerset] at hAS
    have hAI : A ⊆ I := hAS.1.trans (erase_subset _ _)
    have hi0A : i0 ∉ A := fun h => (mem_erase.mp (hAS.1 h)).1 rfl
    have hne : A.Nonempty := by
      have := hAS.2
      simp only [nbr, mem_filter] at this
      obtain ⟨i, hi, -⟩ := this.2
      exact ⟨i, hi⟩
    exact ⟨hAI, hi0A, hne, fun h => hi0A (h ▸ hi0), hAS.2⟩
  obtain ⟨δ, hδpos, hδle, hδeq⟩ : ∃ δ : ℝ, 0 < δ ∧
      (∀ A ∈ S, δ ≤ ∑ j ∈ nbr R J A, ν j - ∑ i ∈ A, μ i) ∧
      (δ = μ i0 ∨ ∃ A ∈ S, ∑ j ∈ nbr R J A, ν j - ∑ i ∈ A, μ i = δ) := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · exact ⟨μ i0, hμpos, by simp [hSe], Or.inl rfl⟩
    · obtain ⟨A, hAS, hAmin⟩ := exists_min_image S
        (fun A => ∑ j ∈ nbr R J A, ν j - ∑ i ∈ A, μ i) hSne
      obtain ⟨hAI, -, hne, hne', -⟩ := hSmem A hAS
      have hle := hH.2.2 A hAI
      have hneq := ht A hAI hne hne'
      refine ⟨_, ?_, hAmin, Or.inr ⟨A, hAS, rfl⟩⟩
      have : ∑ i ∈ A, μ i < ∑ j ∈ nbr R J A, ν j := lt_of_le_of_ne hle hneq
      linarith
  set t := min (min (μ i0) (ν j0)) δ with ht_def
  have htpos : 0 < t := lt_min (lt_min hμpos hνpos) hδpos
  have ht1 : t ≤ μ i0 := (min_le_left _ _).trans (min_le_left _ _)
  have ht2 : t ≤ ν j0 := (min_le_left _ _).trans (min_le_right _ _)
  have ht3 : t ≤ δ := min_le_right _ _
  set μ' : ι → ℝ := fun i => μ i - if i = i0 then t else 0 with hμ'
  set ν' : κ → ℝ := fun j => ν j - if j = j0 then t else 0 with hν'
  have hsumμ : ∀ A : Finset ι, ∑ i ∈ A, μ' i = ∑ i ∈ A, μ i - if i0 ∈ A then t else 0 := by
    intro A; rw [hμ', sum_sub_distrib, sum_ite_eq']
  have hsumν : ∀ B : Finset κ, ∑ j ∈ B, ν' j = ∑ j ∈ B, ν j - if j0 ∈ B then t else 0 := by
    intro B; rw [hν', sum_sub_distrib, sum_ite_eq']
  have hH' : Hall R I J μ' ν' := by
    refine ⟨fun i hi => ?_, fun j hj => ?_, fun A hA => ?_⟩
    · simp only [hμ']; split_ifs with h
      · subst h; linarith
      · simpa using hH.1 i hi
    · simp only [hν']; split_ifs with h
      · subst h; linarith
      · simpa using hH.2.1 j hj
    · rw [hsumμ, hsumν]
      have hle := hH.2.2 A hA
      by_cases hiA : i0 ∈ A
      · have hjA : j0 ∈ nbr R J A := by
          simp only [nbr, mem_filter]; exact ⟨hj0, i0, hiA, hr0⟩
        simp only [hiA, hjA, if_true]; linarith
      · by_cases hjA : j0 ∈ nbr R J A
        · have hAS : A ∈ S := by
            rw [hS, mem_filter, mem_powerset]
            refine ⟨fun x hx => mem_erase.mpr ⟨?_, hA hx⟩, hjA⟩
            rintro rfl; exact hiA hx
          have := hδle A hAS
          simp only [hiA, hjA, if_true, if_false]; linarith
        · simp only [hiA, hjA, if_false]; linarith
  obtain ⟨π', hπ'⟩ : ∃ π, Plan R I J μ' ν' π := by
    rcases min_choice (min (μ i0) (ν j0)) δ with h | h
    · rcases min_choice (μ i0) (ν j0) with h' | h'
      · exact drop μ' ν' hH' (by simp only [hμ', if_true]; rw [← ht_def] at h; linarith)
      · -- ν' j0 = 0: drop the column j0
        have hν0 : ν' j0 = 0 := by simp only [hν', if_true]; rw [← ht_def] at h; linarith
        have hH'' : Hall R I (J.erase j0) μ' ν' := by
          refine ⟨hH'.1, fun j hj => hH'.2.1 j (mem_of_mem_erase hj), fun A hA => ?_⟩
          have : nbr R (J.erase j0) A = (nbr R J A).erase j0 := by
            simp only [nbr]; exact filter_erase _ _ _
          rw [this, sum_erase _ hν0]
          exact hH'.2.2 A hA
        obtain ⟨π, hπ⟩ := IH _ _ μ' ν' (by have := card_erase_lt_of_mem hj0; omega) hH''
        refine ⟨π, hπ.1, fun i j h => ?_, hπ.2.2.1, fun j hj => ?_⟩
        · obtain ⟨a, b, c⟩ := hπ.2.1 i j h; exact ⟨a, mem_of_mem_erase b, c⟩
        · by_cases hjj : j = j0
          · subst hjj; rw [col_zero hπ (fun h => (mem_erase.mp h).1 rfl), hν0]
          · exact hπ.2.2.2 j (mem_erase.mpr ⟨hjj, hj⟩)
    · rcases hδeq with hδμ | ⟨A, hAS, hAeq⟩
      · exact drop μ' ν' hH' (by simp only [hμ', if_true]; rw [← ht_def] at h; linarith)
      · obtain ⟨hAI, hi0A, hne, hne', hjA⟩ := hSmem A hAS
        refine split I J μ' ν' hH' A hAI hne hne' ?_ IH
        rw [hsumμ, hsumν]
        simp only [hi0A, hjA, if_true, if_false]
        rw [← ht_def] at h
        linarith
  exact ⟨_, plan_push htpos.le hi0 hj0 hr0 hπ'⟩

end StrassenA

/-- Child A in the shape of `StrassenPlan.ChildA`. -/
theorem childA (n m : ℕ) (R : Fin n → Fin m → Prop) [DecidableRel R] (μ : Fin n → ℝ)
    (ν : Fin m → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ j, 0 ≤ ν j)
    (hall : ∀ A : Finset (Fin n), ∑ i ∈ A, μ i ≤
        ∑ j ∈ (Finset.univ.filter (fun j => ∃ i ∈ A, R i j) : Finset (Fin m)), ν j) :
    ∃ π : Fin n → Fin m → ℝ, (∀ i j, 0 ≤ π i j) ∧ (∀ i j, ¬ R i j → π i j = 0) ∧
      (∀ i, ∑ j, π i j = μ i) ∧ (∀ j, ∑ i, π i j ≤ ν j) := by
  obtain ⟨π, hπ⟩ := StrassenA.main (R := R) _ Finset.univ Finset.univ μ ν rfl
    ⟨fun i _ => hμ i, fun j _ => hν j, fun A _ => by unfold StrassenA.nbr; convert hall A⟩
  refine ⟨π, hπ.1, fun i j h => ?_, fun i => hπ.2.2.1 i (Finset.mem_univ _),
    fun j => hπ.2.2.2 j (Finset.mem_univ _)⟩
  by_contra h'
  exact h (hπ.2.1 i j h').2.2

end PartA

section PartL
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StrassenL

theorem childLift {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (n m : ℕ)
    (C : Fin n → Set X) (D : Fin m → Set Y) (P₁ : Measure X) (P₂ : Measure Y)
    (hP₁ : IsProbabilityMeasure P₁) (hP₂ : IsProbabilityMeasure P₂)
    (hCm : ∀ i, MeasurableSet (C i)) (hCd : Pairwise (Function.onFun Disjoint C))
    (hCu : (⋃ i, C i) = univ)
    (hDm : ∀ j, MeasurableSet (D j)) (hDd : Pairwise (Function.onFun Disjoint D))
    (hDu : (⋃ j, D j) = univ)
    (π : Fin n → Fin m → ℝ) (hπ : ∀ i j, 0 ≤ π i j)
    (hrow : ∀ i, ∑ j, π i j = (P₁ (C i)).toReal) (hcol : ∀ j, ∑ i, π i j = (P₂ (D j)).toReal) :
    ∃ lam : Measure (X × Y), IsProbabilityMeasure lam ∧ lam.map Prod.fst = P₁ ∧
      lam.map Prod.snd = P₂ ∧ ∀ i j, π i j = 0 → lam (C i ×ˢ D j) = 0 := by
  classical
  have : ∀ i, IsFiniteMeasure (P₁[|C i]) := fun i => inferInstance
  have : ∀ j, IsFiniteMeasure (P₂[|D j]) := fun j => inferInstance
  set lam : Measure (X × Y) :=
    ∑ i, ∑ j, ENNReal.ofReal (π i j) • (P₁[|C i]).prod (P₂[|D j]) with hlam
  -- zero cells carry no coupling mass
  have hz1 : ∀ i j, P₁ (C i) = 0 → π i j = 0 := by
    intro i j h
    have h0 : ∑ j, π i j = 0 := by rw [hrow i, h]; simp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hπ i k)).1 h0 j (Finset.mem_univ _)
  have hz2 : ∀ i j, P₂ (D j) = 0 → π i j = 0 := by
    intro i j h
    have h0 : ∑ i, π i j = 0 := by rw [hcol j, h]; simp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hπ k j)).1 h0 i (Finset.mem_univ _)
  have hu1 : ∀ i j, ENNReal.ofReal (π i j) * P₁[|C i] univ = ENNReal.ofReal (π i j) := by
    intro i j
    by_cases h : P₁ (C i) = 0
    · simp [hz1 i j h]
    · rw [cond_apply (hCm i), inter_univ, ENNReal.inv_mul_cancel h (measure_ne_top _ _), mul_one]
  have hu2 : ∀ i j, ENNReal.ofReal (π i j) * P₂[|D j] univ = ENNReal.ofReal (π i j) := by
    intro i j
    by_cases h : P₂ (D j) = 0
    · simp [hz2 i j h]
    · rw [cond_apply (hDm j), inter_univ, ENNReal.inv_mul_cancel h (measure_ne_top _ _), mul_one]
  have hs1 : ∀ i, ∑ j, ENNReal.ofReal (π i j) = P₁ (C i) := by
    intro i
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hπ i j), hrow i,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hs2 : ∀ j, ∑ i, ENNReal.ofReal (π i j) = P₂ (D j) := by
    intro j
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hπ i j), hcol j,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have htot1 : ∀ s, MeasurableSet s → ∑ i, P₁ (C i ∩ s) = P₁ s := by
    intro s hs
    have := measure_iUnion (μ := P₁) (f := fun i => C i ∩ s)
      (fun a b hab => ((hCd hab).mono inter_subset_left inter_subset_left))
      (fun i => (hCm i).inter hs)
    rw [tsum_fintype, ← iUnion_inter, hCu, univ_inter] at this
    exact this.symm
  have htot2 : ∀ s, MeasurableSet s → ∑ j, P₂ (D j ∩ s) = P₂ s := by
    intro s hs
    have := measure_iUnion (μ := P₂) (f := fun j => D j ∩ s)
      (fun a b hab => ((hDd hab).mono inter_subset_left inter_subset_left))
      (fun j => (hDm j).inter hs)
    rw [tsum_fintype, ← iUnion_inter, hDu, univ_inter] at this
    exact this.symm
  have hfst : lam.map Prod.fst = P₁ := by
    ext s hs
    rw [Measure.map_apply measurable_fst hs, hlam, Measure.coe_finsetSum, Finset.sum_apply]
    have : ∀ i, (∑ j, ENNReal.ofReal (π i j) • (P₁[|C i]).prod (P₂[|D j])) (Prod.fst ⁻¹' s)
        = P₁ (C i ∩ s) := by
      intro i
      rw [Measure.coe_finsetSum, Finset.sum_apply]
      have e : ∀ j, (ENNReal.ofReal (π i j) • (P₁[|C i]).prod (P₂[|D j])) (Prod.fst ⁻¹' s)
          = ENNReal.ofReal (π i j) * P₁[|C i] s := by
        intro j
        rw [Measure.smul_apply, ← prod_univ, Measure.prod_prod, smul_eq_mul, mul_comm (P₁[|C i] s),
          ← mul_assoc, hu2]
      simp_rw [e]
      rw [← Finset.sum_mul, hs1, mul_comm, cond_mul_eq_inter (hCm i)]
    simp_rw [this]
    exact htot1 s hs
  have hsnd : lam.map Prod.snd = P₂ := by
    ext s hs
    rw [Measure.map_apply measurable_snd hs, hlam, Measure.coe_finsetSum, Finset.sum_apply]
    have e : ∀ i j, (ENNReal.ofReal (π i j) • (P₁[|C i]).prod (P₂[|D j])) (Prod.snd ⁻¹' s)
        = ENNReal.ofReal (π i j) * P₂[|D j] s := by
      intro i j
      rw [Measure.smul_apply, ← univ_prod, Measure.prod_prod, smul_eq_mul, ← mul_assoc, hu1]
    simp_rw [Measure.coe_finsetSum, Finset.sum_apply, e]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ i, ENNReal.ofReal (π i j) * P₂[|D j] s = P₂ (D j ∩ s) := by
      intro j
      rw [← Finset.sum_mul, hs2, mul_comm, cond_mul_eq_inter (hDm j)]
    simp_rw [this]
    exact htot2 s hs
  refine ⟨lam, ⟨?_⟩, hfst, hsnd, ?_⟩
  · have h1 : lam univ = (lam.map Prod.fst) univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
    rw [h1, hfst, measure_univ]
  · intro i j hij
    rw [hlam, Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
    by_cases hki : k = i
    · by_cases hlj : l = j
      · subst hki; subst hlj; simp [hij]
      · have : P₂[|D l] (D j) = 0 := by
          rw [cond_apply (hDm l), Disjoint.inter_eq (hDd hlj), measure_empty, mul_zero]
        simp [this]
    · have : P₁[|C k] (C i) = 0 := by
        rw [cond_apply (hCm k), Disjoint.inter_eq (hCd hki), measure_empty, mul_zero]
      simp [this]

end StrassenL

end PartL

section PartC
open MeasureTheory ProbabilityTheory Topology Filter Set Function
open scoped ENNReal NNReal


namespace StrassenC

/-- A weak limit of probability measures whose `f`-images are all `P` has `f`-image `P`. -/
theorem map_eq_of_tendsto {Ω : Type*} {Z : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [TopologicalSpace.PseudoMetrizableSpace Z] [TopologicalSpace.SeparableSpace Z]
    {μs : ℕ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hlim : Tendsto μs atTop (𝓝 μ)) (f : Ω → Z) (hf : Continuous f) (P : Measure Z)
    [IsProbabilityMeasure P] (hP : ∀ n, (μs n : Measure Ω).map f = P) :
    (μ : Measure Ω).map f = P := by
  have hc := ((ProbabilityMeasure.continuous_map hf).tendsto μ).comp hlim
  have hconst : (fun k => ProbabilityMeasure.map (μs k) hf.measurable.aemeasurable)
      = fun _ => (⟨P, inferInstance⟩ : ProbabilityMeasure Z) := by
    funext k
    apply Subtype.ext
    simp [hP]
  rw [comp_def, hconst] at hc
  have := tendsto_nhds_unique tendsto_const_nhds hc
  have h2 := congrArg (fun ν : ProbabilityMeasure Z => (ν : Measure Z)) this
  simpa using h2.symm

/-- Child C: closed-support limit via Prokhorov + portmanteau. -/
theorem childC {X : Type*} {Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (P₁ : Measure X) (P₂ : Measure Y) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (K : Set (X × Y)) (hK : IsClosed K)
    (happ : ∀ U : Set (X × Y), IsOpen U → K ⊆ U → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ lam : Measure (X × Y), IsProbabilityMeasure lam ∧ lam Uᶜ ≤ ε ∧
        lam.map Prod.fst = P₁ ∧ lam.map Prod.snd = P₂) :
    ∃ lam : Measure (X × Y), IsProbabilityMeasure lam ∧ lam Kᶜ = 0 ∧
      lam.map Prod.fst = P₁ ∧ lam.map Prod.snd = P₂ := by
  let _ : MetricSpace (X × Y) := TopologicalSpace.metrizableSpaceMetric (X × Y)
  have hsep : ∀ n : ℕ, ∃ lam : Measure (X × Y), IsProbabilityMeasure lam ∧
      lam (Metric.thickening (1 / ((n : ℝ) + 1)) K)ᶜ ≤ ((n : ℝ≥0∞) + 1)⁻¹ ∧
      lam.map Prod.fst = P₁ ∧ lam.map Prod.snd = P₂ := fun n =>
    happ _ Metric.isOpen_thickening (Metric.self_subset_thickening (by positivity) K) _
      (by simp)
  choose lam hlamP hlamU hlam1 hlam2 using hsep
  let μs : ℕ → ProbabilityMeasure (X × Y) := fun n => ⟨lam n, hlamP n⟩
  have hfst : ∀ n, Measure.fst (lam n) = P₁ := fun n => hlam1 n
  have hsnd : ∀ n, Measure.snd (lam n) = P₂ := fun n => hlam2 n
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure (X × Y)) : Measure (X × Y)) | μ ∈ Set.range μs} := by
    apply IsTightMeasureSet.prodMk
    · refine (isTightMeasureSet_singleton (μ := P₁)).subset ?_
      rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact hfst n
    · refine (isTightMeasureSet_singleton (μ := P₂)).subset ?_
      rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact hsnd n
  have hcomp := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨μ, -, φ, hφ, hlim⟩ :=
    hcomp.tendsto_subseq (x := μs) (fun n => subset_closure (mem_range_self n))
  refine ⟨μ, inferInstance, ?_,
    map_eq_of_tendsto hlim Prod.fst continuous_fst P₁ (fun k => hlam1 (φ k)),
    map_eq_of_tendsto hlim Prod.snd continuous_snd P₂ (fun k => hlam2 (φ k))⟩
  -- support
  have hG : ∀ m : ℕ, (μ : Measure (X × Y)) (Metric.cthickening (1 / ((m : ℝ) + 1)) K)ᶜ = 0 := by
    intro m
    have h1 := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
      (Metric.isClosed_cthickening (δ := 1 / ((m : ℝ) + 1)) (E := K)).isOpen_compl
    refine le_antisymm (h1.trans ?_) bot_le
    have hle : ∀ᶠ k in atTop,
        ((μs ∘ φ) k : Measure (X × Y)) (Metric.cthickening (1 / ((m : ℝ) + 1)) K)ᶜ
          ≤ (k : ℝ≥0∞)⁻¹ := by
      filter_upwards [eventually_ge_atTop m] with k hk
      have hkφ : k ≤ φ k := hφ.id_le k
      calc ((μs ∘ φ) k : Measure (X × Y)) (Metric.cthickening (1 / ((m : ℝ) + 1)) K)ᶜ
          ≤ lam (φ k) (Metric.thickening (1 / ((φ k : ℝ) + 1)) K)ᶜ := by
            apply measure_mono
            apply compl_subset_compl.mpr
            apply Metric.thickening_subset_cthickening_of_le
            have : (m : ℝ) ≤ φ k := by exact_mod_cast hk.trans hkφ
            gcongr
        _ ≤ ((φ k : ℝ≥0∞) + 1)⁻¹ := hlamU (φ k)
        _ ≤ (k : ℝ≥0∞)⁻¹ := by
            apply ENNReal.inv_le_inv.mpr
            calc (k : ℝ≥0∞) ≤ φ k := by exact_mod_cast hkφ
              _ ≤ (φ k : ℝ≥0∞) + 1 := le_self_add
    calc liminf (fun k => ((μs ∘ φ) k : Measure (X × Y))
            (Metric.cthickening (1 / ((m : ℝ) + 1)) K)ᶜ) atTop
        ≤ liminf (fun k : ℕ => (k : ℝ≥0∞)⁻¹) atTop := liminf_le_liminf hle
      _ = 0 := ENNReal.tendsto_inv_nat_nhds_zero.liminf_eq
  have hcov : Kᶜ ⊆ ⋃ m : ℕ, (Metric.cthickening (1 / ((m : ℝ) + 1)) K)ᶜ := by
    intro z hz
    have hz' : z ∉ closure K := by rwa [hK.closure_eq]
    rw [Metric.closure_eq_iInter_cthickening] at hz'
    simp only [mem_iInter, not_forall] at hz'
    obtain ⟨δ, hδ, hzδ⟩ := hz'
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine mem_iUnion.mpr ⟨m, fun hzm => hzδ ?_⟩
    exact Metric.cthickening_mono hm.le K hzm
  exact measure_mono_null hcov (measure_iUnion_null hG)

end StrassenC

end PartC

section PartB
open MeasureTheory ProbabilityTheory Topology Filter Set Function
open scoped ENNReal NNReal


namespace StrassenB

theorem isClosed_upper_of_compact {E : Type*} [MetricSpace E] [PartialOrder E]
    [OrderClosedTopology E] (Q : Set E) (hQ : IsCompact Q) :
    IsClosed {y : E | ∃ x ∈ Q, x ≤ y} := by
  refine isClosed_of_closure_subset (fun y hy => ?_)
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hy
  choose x hxQ hxle using hu
  obtain ⟨a, haQ, φ, hφ, hlimx⟩ := hQ.tendsto_subseq hxQ
  exact ⟨a, haQ, le_of_tendsto_of_tendsto hlimx (hlim.comp hφ.tendsto_atTop)
    (Eventually.of_forall fun n => hxle (φ n))⟩

theorem childB {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (hA : ∀ (n m : ℕ) (R : Fin n → Fin m → Prop) [DecidableRel R] (μ : Fin n → ℝ)
      (ν : Fin m → ℝ),
      (∀ i, 0 ≤ μ i) → (∀ j, 0 ≤ ν j) →
      (∀ A : Finset (Fin n), ∑ i ∈ A, μ i ≤
          ∑ j ∈ (Finset.univ.filter (fun j => ∃ i ∈ A, R i j) : Finset (Fin m)), ν j) →
      ∃ π : Fin n → Fin m → ℝ, (∀ i j, 0 ≤ π i j) ∧ (∀ i j, ¬ R i j → π i j = 0) ∧
        (∀ i, ∑ j, π i j = μ i) ∧ (∀ j, ∑ i, π i j ≤ ν j))
    (hL : ∀ (n m : ℕ) (C : Fin n → Set E) (D : Fin m → Set E) (P₁ : Measure E)
      (P₂ : Measure E),
      IsProbabilityMeasure P₁ → IsProbabilityMeasure P₂ →
      (∀ i, MeasurableSet (C i)) → Pairwise (Disjoint on C) → (⋃ i, C i) = univ →
      (∀ j, MeasurableSet (D j)) → Pairwise (Disjoint on D) → (⋃ j, D j) = univ →
      ∀ π : Fin n → Fin m → ℝ, (∀ i j, 0 ≤ π i j) →
        (∀ i, ∑ j, π i j = (P₁ (C i)).toReal) → (∀ j, ∑ i, π i j = (P₂ (D j)).toReal) →
      ∃ lam : Measure (E × E), IsProbabilityMeasure lam ∧ lam.map Prod.fst = P₁ ∧
        lam.map Prod.snd = P₂ ∧ ∀ i j, π i j = 0 → lam (C i ×ˢ D j) = 0)
    (P₁ P₂ : Measure E) (hP₁ : IsProbabilityMeasure P₁) (hP₂ : IsProbabilityMeasure P₂)
    (h : ∀ B : Set E, IsClosed B → IsUpperSet B → P₁ B ≤ P₂ B)
    (U : Set (E × E)) (hU : IsOpen U) (hKU : {z : E × E | z.1 ≤ z.2} ⊆ U)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ lam : Measure (E × E), IsProbabilityMeasure lam ∧ lam Uᶜ ≤ ε ∧
      lam.map Prod.fst = P₁ ∧ lam.map Prod.snd = P₂ := by
  classical
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨K1, hK1, hK1m⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_singleton (μ := P₁))) (ε / 2) hε2
  obtain ⟨K2, hK2, hK2m⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_singleton (μ := P₂))) (ε / 2) hε2
  letI := TopologicalSpace.metrizableSpaceMetric E
  set Kc : Set E := K1 ∪ K2 with hKcdef
  have hKc : IsCompact Kc := hK1.union hK2
  have hKcc : IsClosed Kc := hKc.isClosed
  have hm1 : P₁ Kcᶜ ≤ ε / 2 :=
    (measure_mono (compl_subset_compl.2 subset_union_left)).trans (hK1m P₁ rfl)
  have hm2 : P₂ Kcᶜ ≤ ε / 2 :=
    (measure_mono (compl_subset_compl.2 subset_union_right)).trans (hK2m P₂ rfl)
  have hKK : IsCompact ({z : E × E | z.1 ≤ z.2} ∩ Kc ×ˢ Kc) :=
    (hKc.prod hKc).inter_left (isClosed_le continuous_fst continuous_snd)
  obtain ⟨δ, hδ, hδU⟩ := hKK.exists_thickening_subset_open hU (inter_subset_left.trans hKU)
  set r : ℝ := δ / 4 with hrdef
  have hr : 0 < r := by rw [hrdef]; positivity
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun x : E => Metric.ball x r)
    (fun _ => Metric.isOpen_ball) (fun y _ => mem_iUnion.2 ⟨y, Metric.mem_ball_self hr⟩)
  set N := t.card
  let c : Fin N → E := fun k => (t.equivFin.symm k : E)
  have hcov : Kc ⊆ ⋃ k, Metric.ball (c k) r := by
    intro y hy
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht hy)
    refine mem_iUnion.2 ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
    simpa [c] using hyx
  let f : Fin N → Set E := fun k => Kc ∩ Metric.ball (c k) r
  have hfm : ∀ k, MeasurableSet (f k) := fun k =>
    hKcc.measurableSet.inter Metric.isOpen_ball.measurableSet
  let C : Fin (N + 1) → Set E := Fin.cases Kcᶜ (fun k => disjointed f k)
  have hC0 : C 0 = Kcᶜ := by simp [C]
  have hCs : ∀ k : Fin N, C k.succ = disjointed f k := by intro k; simp [C]
  have hdm : ∀ k, MeasurableSet (disjointed f k) := by
    intro k
    rw [disjointed_eq_inter_compl]
    exact (hfm k).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hfm j).compl)
  have hCm : ∀ i, MeasurableSet (C i) := by
    intro i
    cases i using Fin.cases with
    | zero => rw [hC0]; exact hKcc.measurableSet.compl
    | succ k => rw [hCs]; exact hdm k
  have hCd : Pairwise (Disjoint on C) := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ l =>
        simp only [onFun, hC0, hCs]
        exact Disjoint.mono_right ((disjointed_subset f l).trans inter_subset_left)
          disjoint_compl_left
    | succ k =>
      cases j using Fin.cases with
      | zero =>
        simp only [onFun, hC0, hCs]
        exact Disjoint.mono_left ((disjointed_subset f k).trans inter_subset_left)
          disjoint_compl_right
      | succ l =>
        simp only [onFun, hCs]
        exact disjoint_disjointed f (fun e => hij (by rw [e]))
  have hCu : (⋃ i, C i) = univ := by
    refine eq_univ_of_forall (fun y => ?_)
    by_cases hy : y ∈ Kc
    · have : y ∈ ⋃ k, f k := by
        obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov hy)
        exact mem_iUnion.2 ⟨k, hy, hk⟩
      rw [← iUnion_disjointed] at this
      obtain ⟨k, hk⟩ := mem_iUnion.1 this
      exact mem_iUnion.2 ⟨k.succ, by rw [hCs]; exact hk⟩
    · exact mem_iUnion.2 ⟨0, by rw [hC0]; exact hy⟩
  have hsub : ∀ i : Fin (N + 1), i ≠ 0 → C i ⊆ Kc ∧ ∃ x, C i ⊆ Metric.ball x r := by
    intro i hi
    cases i using Fin.cases with
    | zero => exact absurd rfl hi
    | succ k =>
      rw [hCs]
      exact ⟨(disjointed_subset f k).trans inter_subset_left,
        c k, (disjointed_subset f k).trans inter_subset_right⟩
  have hclKc : ∀ i : Fin (N + 1), i ≠ 0 → closure (C i) ⊆ Kc := fun i hi =>
    closure_minimal (hsub i hi).1 hKcc
  -- cell masses
  have hsum : ∀ (P : Measure E) [IsProbabilityMeasure P] (A : Finset (Fin (N + 1))),
      ∑ i ∈ A, (P (C i)).toReal = (P (⋃ i ∈ A, C i)).toReal := by
    intro P _ A
    rw [measure_biUnion_finset (hCd.set_pairwise _) (fun i _ => hCm i),
      ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  have huniv : (⋃ i ∈ (Finset.univ : Finset (Fin (N + 1))), C i) = univ := by
    simpa using hCu
  have htot : ∀ (P : Measure E) [IsProbabilityMeasure P],
      ∑ i, (P (C i)).toReal = 1 := by
    intro P _
    rw [hsum P Finset.univ, huniv, measure_univ, ENNReal.toReal_one]
  let R : Fin (N + 1) → Fin (N + 1) → Prop := fun i j =>
    i = 0 ∨ ∃ x ∈ closure (C i), ∃ y ∈ closure (C j), x ≤ y
  obtain ⟨π, hπ0, hπR, hrow, hcolle⟩ := hA (N + 1) (N + 1) R (fun i => (P₁ (C i)).toReal)
    (fun j => (P₂ (C j)).toReal) (fun _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg) (by
      intro A
      by_cases h0 : (0 : Fin (N + 1)) ∈ A
      · have hfil : (Finset.univ.filter (fun j => ∃ i ∈ A, R i j)) = Finset.univ := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact ⟨0, h0, Or.inl rfl⟩
        rw [hfil, htot P₂]
        calc ∑ i ∈ A, (P₁ (C i)).toReal ≤ ∑ i, (P₁ (C i)).toReal :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun _ _ _ => ENNReal.toReal_nonneg)
          _ = 1 := htot P₁
      · rw [hsum P₁, hsum P₂]
        have hi0 : ∀ i ∈ A, i ≠ 0 := fun i hi e => h0 (e ▸ hi)
        set Q : Set E := ⋃ i ∈ A, closure (C i)
        have hQ : IsCompact Q := A.isCompact_biUnion (fun i hi =>
          hKc.of_isClosed_subset isClosed_closure (hclKc i (hi0 i hi)))
        have hB := isClosed_upper_of_compact Q hQ
        have hBu : IsUpperSet {y : E | ∃ x ∈ Q, x ≤ y} :=
          fun a b hab ⟨x, hx, hxa⟩ => ⟨x, hx, hxa.trans hab⟩
        refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
        refine le_trans (measure_mono ?_) (le_trans (h _ hB hBu) (measure_mono ?_))
        · intro y hy
          obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
          exact ⟨y, mem_iUnion₂.2 ⟨i, hi, subset_closure hyi⟩, le_rfl⟩
        · rintro y ⟨x, hx, hxy⟩
          obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx
          obtain ⟨j, hj⟩ := mem_iUnion.1 (hCu.symm ▸ mem_univ y : y ∈ ⋃ j, C j)
          refine mem_iUnion₂.2 ⟨j, ?_, hj⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨i, hi, Or.inr ⟨x, hxi, y, subset_closure hj, hxy⟩⟩)
  have hcol : ∀ j, ∑ i, π i j = (P₂ (C j)).toReal := by
    have htotπ : ∑ j, ∑ i, π i j = ∑ j, (P₂ (C j)).toReal := by
      rw [Finset.sum_comm, Finset.sum_congr rfl (fun i _ => hrow i), htot P₁, htot P₂]
    intro j
    exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hcolle j)).1 htotπ j (Finset.mem_univ _)
  obtain ⟨lam, hlamP, hfst, hsnd, hzero⟩ :=
    hL (N + 1) (N + 1) C C P₁ P₂ hP₁ hP₂ hCm hCd hCu hCm hCd hCu π hπ0 hrow hcol
  refine ⟨lam, hlamP, ?_, hfst, hsnd⟩
  have hcover : Uᶜ ⊆ (C 0 ×ˢ univ ∪ univ ×ˢ C 0) ∪
      ⋃ i, ⋃ j, ⋃ (_ : ¬ R i j), C i ×ˢ C j := by
    rintro ⟨a, b⟩ hab
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hCu.symm ▸ mem_univ a : a ∈ ⋃ i, C i)
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hCu.symm ▸ mem_univ b : b ∈ ⋃ j, C j)
    by_cases hi0 : i = 0
    · subst hi0; exact Or.inl (Or.inl ⟨hi, mem_univ _⟩)
    by_cases hj0 : j = 0
    · subst hj0; exact Or.inl (Or.inr ⟨mem_univ _, hj⟩)
    by_cases hR : R i j
    · exfalso
      apply hab
      rcases hR with hR | ⟨x, hx, y, hy, hxy⟩
      · exact absurd hR hi0
      obtain ⟨ci, hci⟩ := (hsub i hi0).2
      obtain ⟨cj, hcj⟩ := (hsub j hj0).2
      have hxc : x ∈ Metric.closedBall ci r :=
        closure_minimal (hci.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall hx
      have hyc : y ∈ Metric.closedBall cj r :=
        closure_minimal (hcj.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall hy
      have hac := hci hi
      have hbc := hcj hj
      rw [Metric.mem_closedBall] at hxc hyc
      rw [Metric.mem_ball] at hac hbc
      apply hδU
      rw [Metric.mem_thickening_iff]
      refine ⟨(x, y), ⟨hxy, hclKc i hi0 hx, hclKc j hj0 hy⟩, ?_⟩
      rw [Prod.dist_eq]
      have h1 : dist a x < δ := by
        have := dist_triangle_right a x ci; linarith
      have h2 : dist b y < δ := by
        have := dist_triangle_right b y cj; linarith
      exact max_lt h1 h2
    · exact Or.inr (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hR, hi, hj⟩⟩⟩)
  have hnull : lam (⋃ i, ⋃ j, ⋃ (_ : ¬ R i j), C i ×ˢ C j) = 0 :=
    measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hR =>
      hzero i j (hπR i j hR)
  have hl1 : lam (C 0 ×ˢ univ) ≤ ε / 2 := by
    rw [prod_univ, ← Measure.map_apply measurable_fst (hCm 0), hfst, hC0]; exact hm1
  have hl2 : lam (univ ×ˢ C 0) ≤ ε / 2 := by
    rw [univ_prod, ← Measure.map_apply measurable_snd (hCm 0), hsnd, hC0]; exact hm2
  calc lam Uᶜ ≤ lam ((C 0 ×ˢ univ ∪ univ ×ˢ C 0) ∪
        ⋃ i, ⋃ j, ⋃ (_ : ¬ R i j), C i ×ˢ C j) := measure_mono hcover
    _ ≤ lam (C 0 ×ˢ univ ∪ univ ×ˢ C 0) + lam (⋃ i, ⋃ j, ⋃ (_ : ¬ R i j), C i ×ˢ C j) :=
        measure_union_le _ _
    _ ≤ (lam (C 0 ×ˢ univ) + lam (univ ×ˢ C 0)) + 0 := by
        rw [hnull]; gcongr; exact measure_union_le _ _
    _ ≤ (ε / 2 + ε / 2) + 0 := by gcongr
    _ = ε := by rw [add_zero, ENNReal.add_halves]

end StrassenB

end PartB

open MeasureTheory ProbabilityTheory in
theorem solution {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P₁ P₂ : Measure E) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h : ∀ B : Set E, IsClosed B → IsUpperSet B → P₁ B ≤ P₂ B) :
    ∃ lam : Measure (E × E), IsProbabilityMeasure lam ∧ lam {z : E × E | z.1 ≤ z.2}ᶜ = 0 ∧
      lam.map Prod.fst = P₁ ∧ lam.map Prod.snd = P₂ := by
  exact StrassenC.childC P₁ P₂ {z : E × E | z.1 ≤ z.2}
    (isClosed_le continuous_fst continuous_snd)
    (fun U hU hKU ε hε => StrassenB.childB (@childA)
      (fun n m C D Q₁ Q₂ => StrassenL.childLift n m C D Q₁ Q₂)
      P₁ P₂ inferInstance inferInstance h U hU hKU ε hε)
