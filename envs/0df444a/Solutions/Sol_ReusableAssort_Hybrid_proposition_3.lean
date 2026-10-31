-- Prove2me | solution 1 for ReusableAssort.Hybrid.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:26:19.226038+00:00
-- url     : https://prove2.me/submissions/88dd5ac3-b13f-4ac5-97a0-ea31072f7a7e

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_SubAssort

open ReusableAssort.Hybrid

private lemma telesc (f : ℕ → ℝ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, (f (j - 1) - f j) = f (a - 1) - f (b - 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    have : b + 1 - 1 = b := by omega
    rw [this]
    have : b - 1 + 1 = b := by omega
    ring

/-- Removing products from a feasible assortment can only increase the choice probabilities
(iterated weak substitutability). -/
private lemma phi_mono {n : ℕ} (φ : Finset (Fin n) → Fin n → ℝ)
    (feas : Finset (Finset (Fin n)))
    (h_subst : ∀ S ∈ feas, ∀ i j, j ≠ i → insert j S ∈ feas → φ (insert j S) i ≤ φ S i)
    (h_down : ∀ S ∈ feas, ∀ S' ⊆ S, S' ∈ feas) :
    ∀ S ∈ feas, ∀ S' ⊆ S, ∀ i ∈ S', φ S i ≤ φ S' i := by
  have key : ∀ D : Finset (Fin n), ∀ S' : Finset (Fin n), S' ∪ D ∈ feas →
      ∀ i ∈ S', φ (S' ∪ D) i ≤ φ S' i := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro S' _ i _; simp
    | insert a D haD ih =>
      intro S' hfe i hi
      rw [Finset.union_insert] at hfe ⊢
      have hfe' : S' ∪ D ∈ feas := h_down _ hfe _ (Finset.subset_insert _ _)
      by_cases ha : a ∈ S' ∪ D
      · rw [Finset.insert_eq_of_mem ha]
        exact ih S' hfe' i hi
      · have hai : a ≠ i := by
          rintro rfl; exact ha (Finset.mem_union_left _ hi)
        exact (h_subst _ hfe' i a hai hfe).trans (ih S' hfe' i hi)
  intro S hS S' hS' i hi
  have := key (S \ S') S' (by rwa [Finset.union_sdiff_of_subset hS']) i hi
  rwa [Finset.union_sdiff_of_subset hS'] at this

theorem solution {n : ℕ} (φ : Finset (Fin n) → Fin n → ℝ)
    (feas : Finset (Finset (Fin n)))
    (h_empty : ∀ i, φ ∅ i = 0)
    (h_subst : ∀ S ∈ feas, ∀ i j, j ≠ i → insert j S ∈ feas → φ (insert j S) i ≤ φ S i)
    (h_down : ∀ S ∈ feas, ∀ S' ⊆ S, S' ∈ feas)
    (h_nonneg : ∀ S ∈ feas, ∀ i, 0 ≤ φ S i)
    (h_supp : ∀ S ∈ feas, ∀ i, i ∉ S → φ S i = 0)
    (h_sum : ∀ S ∈ feas, ∑ i ∈ S, φ S i ≤ 1)
    (S : Finset (Fin n)) (hS : S ∈ feas)
    (p : Fin n → ℝ) (hp : ∀ i ∈ S, 0 ≤ p i ∧ p i ≤ φ S i) :
    (∀ U, subAssort φ S p U ≠ 0 → U ⊆ S) ∧
    (∀ U, 0 ≤ subAssort φ S p U) ∧
    ∑ U ∈ S.powerset, subAssort φ S p U = 1 ∧
    ∀ i ∈ S, ∑ U ∈ S.powerset, subAssort φ S p U * φ U i = p i := by
  have hmono := phi_mono φ feas h_subst h_down
  -- the empty-output distribution
  have hempty : ∀ S : Finset (Fin n), S = ∅ → ∀ (f : Finset (Fin n) → ℝ),
      (∀ U, f U = if U = ∅ then 1 else 0) →
      (∀ U, f U ≠ 0 → U ⊆ S) ∧ (∀ U, 0 ≤ f U) ∧ ∑ U ∈ S.powerset, f U = 1 ∧
      ∀ i ∈ S, ∑ U ∈ S.powerset, f U * φ U i = p i := by
    intro S hS0 f hf
    subst hS0
    refine ⟨fun U hU => ?_, fun U => ?_, ?_, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · rw [hf] at hU; split_ifs at hU with h
      · rw [h]
      · exact absurd rfl hU
    · rw [hf]; split_ifs <;> norm_num
    · simp [hf]
  suffices H : ∀ k : ℕ, ∀ S ∈ feas, S.card ≤ k → ∀ p : Fin n → ℝ,
      (∀ i ∈ S, 0 ≤ p i ∧ p i ≤ φ S i) →
      (∀ U, subAssortAux k φ S p U ≠ 0 → U ⊆ S) ∧
      (∀ U, 0 ≤ subAssortAux k φ S p U) ∧
      ∑ U ∈ S.powerset, subAssortAux k φ S p U = 1 ∧
      ∀ i ∈ S, ∑ U ∈ S.powerset, subAssortAux k φ S p U * φ U i = p i by
    exact H S.card S hS le_rfl p hp
  intro k
  induction k with
  | zero =>
    intro S _ hc p _
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hc)
    subst hS0
    refine ⟨fun U hU => ?_, fun U => ?_, ?_, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · simp only [subAssortAux] at hU; split_ifs at hU with h
      · rw [h]
      · exact absurd rfl hU
    · simp only [subAssortAux]; split_ifs <;> norm_num
    · simp [subAssortAux]
  | succ k ih =>
    intro S hS hc p hp
    by_cases hS0 : S = ∅
    · subst hS0
      refine ⟨fun U hU => ?_, fun U => ?_, ?_, fun i hi => absurd hi (Finset.notMem_empty i)⟩
      · simp only [subAssortAux, if_true] at hU; split_ifs at hU with h
        · rw [h]
        · exact absurd rfl hU
      · simp only [subAssortAux, if_true]; split_ifs <;> norm_num
      · simp [subAssortAux]
    set m := S.card with hm
    have hm1 : 1 ≤ m := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS0)
    set L := sortedList φ S p with hL
    have hLperm : L.Perm (S.sort (· ≤ ·)) := List.mergeSort_perm _ _
    have hLnodup : L.Nodup := hLperm.nodup_iff.mpr (Finset.sort_nodup _ _)
    have hLmem : ∀ a, a ∈ L ↔ a ∈ S := fun a =>
      hLperm.mem_iff.trans (Finset.mem_sort _)
    have hLlen : L.length = m := hLperm.length_eq.trans (Finset.length_sort _)
    set ρ := ratio φ S p with hρ
    have hLsorted : L.Pairwise (fun a b => decide (ρ b ≤ ρ a) = true) := by
      apply List.pairwise_mergeSort
      · intro a b c hab hbc
        simp only [decide_eq_true_eq] at hab hbc ⊢; linarith
      · intro a b
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _
    -- ratio bounds
    have hρ01 : ∀ a ∈ S, 0 ≤ ρ a ∧ ρ a ≤ 1 := by
      intro a ha
      simp only [hρ, ratio]
      split_ifs with h0
      · norm_num
      · have hφ : 0 < φ S a := lt_of_le_of_ne (h_nonneg S hS a) (Ne.symm h0)
        exact ⟨div_nonneg (hp a ha).1 hφ.le, (div_le_one hφ).mpr (hp a ha).2⟩
    have hρp : ∀ a ∈ S, φ S a * ρ a = p a := by
      intro a ha
      simp only [hρ, ratio]
      split_ifs with h0
      · rw [h0]; linarith [(hp a ha).1, (hp a ha).2, h0]
      · field_simp
    set rr : ℕ → ℝ := fun j => (L.map ρ).getD j 0 with hrr
    have hrrL : ∀ j (h : j < L.length), rr j = ρ L[j] := by
      intro j h
      simp [hrr, List.getD_eq_getElem?_getD, h]
    have hLS : ∀ j (h : j < L.length), L[j] ∈ S := fun j h => (hLmem _).mp (List.getElem_mem h)
    have hanti : ∀ j j', j ≤ j' → j' < m → rr j' ≤ rr j := by
      intro j j' hjj hj'
      rcases hjj.eq_or_lt with h | h
      · rw [h]
      · rw [hrrL j (by omega), hrrL j' (by omega)]
        have := List.pairwise_iff_getElem.mp hLsorted j j' (by omega) (by omega) h
        simpa using this
    have hq : ∀ j, qprob φ S p j =
        if j = 0 then 1 - rr 0 else if j = m then rr (m - 1) else rr (j - 1) - rr j := by
      intro j; rfl
    have hq0 : 0 ≤ qprob φ S p 0 := by
      rw [hq]; simp only [if_true]
      rw [hrrL 0 (by omega)]; linarith [(hρ01 _ (hLS 0 (by omega))).2]
    have hqm : 0 ≤ qprob φ S p m := by
      rw [hq, if_neg (by omega), if_pos rfl, hrrL (m - 1) (by omega)]
      exact (hρ01 _ (hLS _ _)).1
    have hqj : ∀ j ∈ Finset.Ico 1 m, qprob φ S p j = rr (j - 1) - rr j := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [hq, if_neg (by omega), if_neg (by omega)]
    have hqj0 : ∀ j ∈ Finset.Ico 1 m, 0 ≤ qprob φ S p j := by
      intro j hj
      rw [hqj j hj]
      have := Finset.mem_Ico.mp hj
      linarith [hanti (j - 1) j (by omega) (by omega)]
    -- the recursive calls
    set Sj : ℕ → Finset (Fin n) := fun j => (L.take j).toFinset with hSj
    have hSjS : ∀ j, Sj j ⊆ S := by
      intro j a ha
      simp only [hSj, List.mem_toFinset] at ha
      exact (hLmem a).mp (List.mem_of_mem_take ha)
    have hSjcard : ∀ j ≤ m, (Sj j).card = j := by
      intro j hj
      simp only [hSj]
      rw [List.toFinset_card_of_nodup (hLnodup.sublist (List.take_sublist _ _)),
        List.length_take, hLlen]
      omega
    have hIH : ∀ j ∈ Finset.Ico 1 m, _ := fun j hj =>
      ih (Sj j) (h_down S hS _ (hSjS j)) (by
        rw [hSjcard j (by have := Finset.mem_Ico.mp hj; omega)]
        have := Finset.mem_Ico.mp hj; omega) (φ S)
        (fun a ha => ⟨h_nonneg S hS a, hmono S hS _ (hSjS j) a ha⟩)
    -- membership in the top-`j` set
    have hpos : ∀ a ∈ S, ∀ j, a ∈ Sj j ↔ L.idxOf a < j := by
      intro a ha j
      have haL : a ∈ L := (hLmem a).mpr ha
      have hidx : L.idxOf a < L.length := List.idxOf_lt_length_of_mem haL
      simp only [hSj, List.mem_toFinset, List.mem_take_iff_getElem]
      constructor
      · rintro ⟨i, hi, rfl⟩
        rw [hLnodup.idxOf_getElem]
        omega
      · intro h
        exact ⟨L.idxOf a, by omega, List.getElem_idxOf hidx⟩
    -- unfolding one step of the procedure
    have hunf : ∀ U, subAssortAux (k + 1) φ S p U =
        qprob φ S p 0 * (if U = ∅ then 1 else 0)
          + qprob φ S p m * (if U = S then 1 else 0)
          + ∑ j ∈ Finset.Ico 1 m, qprob φ S p j * subAssortAux k φ (Sj j) (φ S) U := by
      intro U
      rw [subAssortAux, if_neg hS0]
    -- restricting a sum over `S.powerset` to `(Sj j).powerset`
    have hrestrict : ∀ j ∈ Finset.Ico 1 m, ∀ g : Finset (Fin n) → ℝ,
        ∑ U ∈ S.powerset, subAssortAux k φ (Sj j) (φ S) U * g U
          = ∑ U ∈ (Sj j).powerset, subAssortAux k φ (Sj j) (φ S) U * g U := by
      intro j hj g
      symm
      apply Finset.sum_subset
      · intro U hU
        exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hU).trans (hSjS j))
      · intro U _ hU
        have : subAssortAux k φ (Sj j) (φ S) U = 0 := by
          by_contra h
          exact hU (Finset.mem_powerset.mpr ((hIH j hj).1 U h))
        rw [this, zero_mul]
    have hsumq : qprob φ S p 0 + qprob φ S p m + ∑ j ∈ Finset.Ico 1 m, qprob φ S p j = 1 := by
      rw [Finset.sum_congr rfl hqj, telesc rr (le_refl 1) hm1, hq 0, hq m, if_pos rfl,
        if_neg (by omega), if_pos rfl]
      simp
    refine ⟨fun U hU => ?_, fun U => ?_, ?_, fun i hi => ?_⟩
    · -- support
      rw [hunf] at hU
      by_cases hU0 : U = ∅
      · rw [hU0]; exact Finset.empty_subset _
      by_cases hUS : U = S
      · rw [hUS]
      simp only [hU0, hUS, if_false, mul_zero, zero_add] at hU
      obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU
      have : subAssortAux k φ (Sj j) (φ S) U ≠ 0 := by
        intro h; rw [h, mul_zero] at hne; exact hne rfl
      exact ((hIH j hj).1 U this).trans (hSjS j)
    · -- nonnegativity
      rw [hunf]
      refine add_nonneg (add_nonneg ?_ ?_) (Finset.sum_nonneg fun j hj =>
        mul_nonneg (hqj0 j hj) ((hIH j hj).2.1 U))
      · exact mul_nonneg hq0 (by split_ifs <;> norm_num)
      · exact mul_nonneg hqm (by split_ifs <;> norm_num)
    · -- total mass
      simp_rw [hunf]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
      have h1 : ∑ U ∈ S.powerset, qprob φ S p 0 * (if U = ∅ then (1 : ℝ) else 0)
          = qprob φ S p 0 := by
        simp [← Finset.mul_sum, Finset.sum_ite_eq']
      have h2 : ∑ U ∈ S.powerset, qprob φ S p m * (if U = S then (1 : ℝ) else 0)
          = qprob φ S p m := by
        simp [← Finset.mul_sum, Finset.sum_ite_eq']
      have h3 : ∀ j ∈ Finset.Ico 1 m, ∑ U ∈ S.powerset,
          qprob φ S p j * subAssortAux k φ (Sj j) (φ S) U = qprob φ S p j := by
        intro j hj
        rw [← Finset.mul_sum]
        have := hrestrict j hj (fun _ => 1)
        simp only [mul_one] at this
        rw [this, (hIH j hj).2.2.1, mul_one]
      rw [h1, h2, Finset.sum_congr rfl h3, hsumq]
    · -- marginals
      simp_rw [hunf, add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have h1 : ∑ U ∈ S.powerset, qprob φ S p 0 * (if U = ∅ then (1 : ℝ) else 0) * φ U i
          = 0 := by
        refine Finset.sum_eq_zero fun U _ => ?_
        split_ifs with h
        · rw [h, h_empty]; ring
        · ring
      have h2 : ∑ U ∈ S.powerset, qprob φ S p m * (if U = S then (1 : ℝ) else 0) * φ U i
          = qprob φ S p m * φ S i := by
        rw [Finset.sum_eq_single S]
        · simp
        · intro U _ hU; simp [hU]
        · intro h; exact absurd (Finset.mem_powerset_self S) h
      set pos := L.idxOf i with hposdef
      have hposlt : pos < m := by
        rw [← hLlen]; exact List.idxOf_lt_length_of_mem ((hLmem i).mpr hi)
      have h3 : ∀ j ∈ Finset.Ico 1 m, ∑ U ∈ S.powerset,
          (∑ j' ∈ Finset.Ico 1 m, qprob φ S p j' * subAssortAux k φ (Sj j') (φ S) U) * φ U i
          = ∑ U ∈ S.powerset,
          (∑ j' ∈ Finset.Ico 1 m, qprob φ S p j' * subAssortAux k φ (Sj j') (φ S) U) * φ U i :=
        fun _ _ => rfl
      clear h3
      have hinner : ∀ j ∈ Finset.Ico 1 m, ∑ U ∈ S.powerset,
          subAssortAux k φ (Sj j) (φ S) U * φ U i
          = if pos < j then φ S i else 0 := by
        intro j hj
        rw [hrestrict j hj (fun U => φ U i)]
        split_ifs with hpj
        · exact (hIH j hj).2.2.2 i ((hpos i hi j).mpr hpj)
        · refine Finset.sum_eq_zero fun U hU => ?_
          have hUsub := Finset.mem_powerset.mp hU
          have hiU : i ∉ U := fun h => hpj ((hpos i hi j).mp (hUsub h))
          rw [h_supp U (h_down S hS U (hUsub.trans (hSjS j))) i hiU, mul_zero]
      have hmid : ∑ U ∈ S.powerset,
          (∑ j ∈ Finset.Ico 1 m, qprob φ S p j * subAssortAux k φ (Sj j) (φ S) U) * φ U i
          = φ S i * (rr pos - rr (m - 1)) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        have : ∀ j ∈ Finset.Ico 1 m, ∑ U ∈ S.powerset,
            qprob φ S p j * subAssortAux k φ (Sj j) (φ S) U * φ U i
            = qprob φ S p j * (if pos < j then φ S i else 0) := by
          intro j hj
          rw [← hinner j hj, Finset.mul_sum]
          refine Finset.sum_congr rfl fun U _ => by ring
        rw [Finset.sum_congr rfl this]
        have : ∑ j ∈ Finset.Ico 1 m, qprob φ S p j * (if pos < j then φ S i else 0)
            = φ S i * ∑ j ∈ Finset.Ico (pos + 1) m, (rr (j - 1) - rr j) := by
          rw [Finset.mul_sum]
          rw [← Finset.sum_subset (s₁ := Finset.Ico (pos + 1) m) (s₂ := Finset.Ico 1 m)]
          · refine Finset.sum_congr rfl fun j hj => ?_
            have hj' := Finset.mem_Ico.mp hj
            rw [if_pos (by omega), hqj j (Finset.mem_Ico.mpr ⟨by omega, hj'.2⟩)]
            ring
          · intro j hj
            have := Finset.mem_Ico.mp hj
            exact Finset.mem_Ico.mpr ⟨by omega, this.2⟩
          · intro j hj1 hj
            rw [Finset.mem_Ico] at hj hj1
            rw [if_neg (by omega), mul_zero]
        rw [this, telesc rr (by omega) (by omega)]
        simp
      rw [h1, h2, hmid]
      have hrrpos : rr pos = ρ i := by
        rw [hrrL pos (by omega)]
        congr 1
        exact List.getElem_idxOf (by omega)
      rw [hrrpos]
      have hmm : qprob φ S p m = rr (m - 1) := by
        rw [hq, if_neg (by omega), if_pos rfl]
      rw [hmm, ← hρp i hi]
      ring
