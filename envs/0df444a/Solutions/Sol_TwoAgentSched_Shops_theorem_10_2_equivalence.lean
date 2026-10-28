-- Prove2me | solution 1 for TwoAgentSched.Shops.theorem_10_2_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:09:28.920242+00:00
-- url     : https://prove2.me/submissions/08d8233a-7330-47c7-8591-c46bc9ba2fb4

import Mathlib
import Definitions.Def_TwoAgentSched_Shops_Construction
import Theorems.Thm_TwoAgentSched_Shops_open_bjob_starts

open TwoAgentSched.Shops ProjSchedTW.Complexity

private lemma nonoverlap_sum_le {α : Type*} [DecidableEq α] (a L : α → ℝ)
    (hL : ∀ i, 0 ≤ L i)
    (hdisj : ∀ i j, i ≠ j → a i + L i ≤ a j ∨ a j + L j ≤ a i) :
    ∀ (n : ℕ) (T : Finset α), T.card = n → ∀ (lo hi : ℝ), lo ≤ hi →
      (∀ i ∈ T, lo ≤ a i ∧ a i + L i ≤ hi) → ∑ i ∈ T, L i ≤ hi - lo := by
  intro n
  induction n with
  | zero =>
    intro T hcard lo hi hle _
    rw [Finset.card_eq_zero.mp hcard, Finset.sum_empty]
    linarith
  | succ n ih =>
    intro T hcard lo hi hle hT
    by_cases hzero : ∃ i₀ ∈ T, L i₀ = 0
    · obtain ⟨i₀, hi₀, hLi₀⟩ := hzero
      rw [← Finset.add_sum_erase _ _ hi₀, hLi₀, zero_add]
      exact ih (T.erase i₀) (by rw [Finset.card_erase_of_mem hi₀, hcard]; rfl) lo hi hle
        (fun i hi => hT i (Finset.mem_of_mem_erase hi))
    · push_neg at hzero
      have hpos : ∀ i ∈ T, 0 < L i := fun i hi => lt_of_le_of_ne (hL i) (Ne.symm (hzero i hi))
      have hne : T.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image T a hne
      rw [← Finset.add_sum_erase _ _ hi₀]
      have hi₀_bounds := hT i₀ hi₀
      have hsub : ∑ i ∈ T.erase i₀, L i ≤ hi - (a i₀ + L i₀) := by
        refine ih (T.erase i₀) (by rw [Finset.card_erase_of_mem hi₀, hcard]; rfl)
          (a i₀ + L i₀) hi hi₀_bounds.2 (fun j hj => ?_)
        have hjT : j ∈ T := Finset.mem_of_mem_erase hj
        have hne_ji : i₀ ≠ j := (Finset.ne_of_mem_erase hj).symm
        have haj : a i₀ ≤ a j := hmin j hjT
        have hLj : 0 < L j := hpos j hjT
        rcases hdisj i₀ j hne_ji with h1 | h2
        · exact ⟨h1, (hT j hjT).2⟩
        · linarith
      linarith

private lemma sum_get_eq_sum (p : List ℕ) : ∑ i : Fin p.length, p.get i = p.sum := by
  induction p with
  | nil => simp
  | cons a l ih =>
    change ∑ i : Fin (l.length + 1), (a :: l).get i = (a :: l).sum
    rw [Fin.sum_univ_succ]
    simp [ih]

private lemma sum_get_real_eq_partSum (p : List ℕ) :
    ∑ i : Fin p.length, (p.get i : ℝ) = partSum p := by
  unfold partSum
  rw [← sum_get_eq_sum p]
  push_cast
  rfl

private def cum {k : ℕ} (w : Fin k → ℝ) (S : Finset (Fin k)) (i : Fin k) : ℝ :=
  ∑ j ∈ S.filter (· < i), w j

private lemma cum_nonneg {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 ≤ w i) (S : Finset (Fin k)) (i : Fin k) :
    0 ≤ cum w S i :=
  Finset.sum_nonneg (fun j _ => hw j)

private lemma cum_add_le_sum {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 ≤ w i)
    {S : Finset (Fin k)} {i : Fin k} (hi : i ∈ S) :
    cum w S i + w i ≤ ∑ j ∈ S, w j := by
  unfold cum
  have hnot : i ∉ S.filter (· < i) := by simp
  rw [add_comm, ← Finset.sum_insert hnot]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hw j)
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact hi
  · exact (Finset.mem_filter.mp hj).1

private lemma cum_add_le_cum_of_lt {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 ≤ w i)
    {S : Finset (Fin k)} {i j : Fin k} (hi : i ∈ S) (hij : i < j) :
    cum w S i + w i ≤ cum w S j := by
  unfold cum
  have hnot : i ∉ S.filter (· < i) := by simp
  rw [add_comm, ← Finset.sum_insert hnot]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hw x)
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_filter.mpr ⟨hi, hij⟩
  · obtain ⟨hxS, hxi⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxS, lt_trans hxi hij⟩

private lemma cum_disj {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 ≤ w i)
    {S : Finset (Fin k)} {i j : Fin k} (hi : i ∈ S) (hj : j ∈ S) (hne : i ≠ j) (t₀ : ℝ) :
    (t₀ + cum w S i) + w i ≤ t₀ + cum w S j ∨ (t₀ + cum w S j) + w j ≤ t₀ + cum w S i := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · left; linarith [cum_add_le_cum_of_lt hw hi hij]
  · right; linarith [cum_add_le_cum_of_lt hw hj hji]

private lemma partition_of_b_at_half (p : List ℕ)
    (σ : Fin ((openInst p).nA + (openInst p).nB) → ℝ)
    (h0 : ∀ j, 0 ≤ σ j)
    (hdisj : ∀ i j, i ≠ j →
      σ i + (openInst p).p1 i ≤ σ j ∨ σ j + (openInst p).p1 j ≤ σ i)
    (hB_half : σ (openB p) = partSum p / 2)
    (hA_end : ∀ h : Fin p.length, σ ((openInst p).aJob h) + (p.get h : ℝ) ≤ 3 * partSum p / 2) :
    PartitionYes p := by
  classical
  have hb : finSumFinEquiv.symm (openB p) = Sum.inr ⟨0, Nat.one_pos⟩ :=
    finSumFinEquiv_symm_apply_natAdd ⟨0, Nat.one_pos⟩
  have hpB : (openInst p).p1 (openB p) = partSum p / 2 := by
    unfold Instance.p1; rw [hb]; rfl
  have ha : ∀ i : Fin p.length, finSumFinEquiv.symm ((openInst p).aJob i) = Sum.inl i :=
    fun i => finSumFinEquiv_symm_apply_castAdd i
  have hpA : ∀ i : Fin p.length, (openInst p).p1 ((openInst p).aJob i) = (p.get i : ℝ) := by
    intro i; unfold Instance.p1; rw [ha i]; rfl
  have ha_inj : Function.Injective (openInst p).aJob := by
    intro i j hij
    have := congrArg finSumFinEquiv.symm hij
    rw [ha i, ha j] at this
    exact Sum.inl_injective this
  have ha_ne_B : ∀ i : Fin p.length, (openInst p).aJob i ≠ openB p := by
    intro i h
    have := congrArg finSumFinEquiv.symm h
    rw [ha i, hb] at this
    nomatch this
  set A := Finset.univ.filter
    (fun i : Fin p.length => σ ((openInst p).aJob i) + (p.get i : ℝ) ≤ partSum p / 2)
  have hP_nonneg : 0 ≤ partSum p := by unfold partSum; positivity
  have hsumA : ∑ i ∈ A, (p.get i : ℝ) ≤ partSum p / 2 := by
    have := nonoverlap_sum_le (fun i : Fin p.length => σ ((openInst p).aJob i))
      (fun i : Fin p.length => (p.get i : ℝ)) (fun i => by positivity)
      (fun i j hij => by
        have := hdisj ((openInst p).aJob i) ((openInst p).aJob j) (fun e => hij (ha_inj e))
        rwa [hpA i, hpA j] at this)
      A.card A rfl 0 (partSum p / 2) (by linarith)
      (fun i hi => ⟨h0 ((openInst p).aJob i), (Finset.mem_filter.mp hi).2⟩)
    linarith
  have hsumAc : ∑ i ∈ Aᶜ, (p.get i : ℝ) ≤ partSum p / 2 := by
    have := nonoverlap_sum_le (fun i : Fin p.length => σ ((openInst p).aJob i))
      (fun i : Fin p.length => (p.get i : ℝ)) (fun i => by positivity)
      (fun i j hij => by
        have := hdisj ((openInst p).aJob i) ((openInst p).aJob j) (fun e => hij (ha_inj e))
        rwa [hpA i, hpA j] at this)
      Aᶜ.card Aᶜ rfl (partSum p) (3 * partSum p / 2) (by linarith)
      (fun i hi => by
        have hnotA : ¬ (σ ((openInst p).aJob i) + (p.get i : ℝ) ≤ partSum p / 2) := by
          simpa [A] using hi
        have hdisjB := hdisj ((openInst p).aJob i) (openB p) (ha_ne_B i)
        rw [hpA i, hpB, hB_half] at hdisjB
        rcases hdisjB with h1 | h2
        · exact absurd h1 hnotA
        · exact ⟨by linarith, hA_end i⟩)
    linarith
  have htot : ∑ i ∈ A, (p.get i : ℝ) + ∑ i ∈ Aᶜ, (p.get i : ℝ) = partSum p := by
    rw [Finset.sum_add_sum_compl, sum_get_real_eq_partSum]
  have heq_real : ∑ i ∈ A, (p.get i : ℝ) = ∑ i ∈ Aᶜ, (p.get i : ℝ) := by linarith
  refine ⟨A, ?_⟩
  exact_mod_cast heq_real

open Classical in
theorem solution (p : List ℕ) :
    PartitionYes p ↔ (openInst p).OpenYes (openQA p) (openQB p) := by
  constructor
  · rintro ⟨A, hA⟩
    have hA_real : ∑ i ∈ A, (p.get i : ℝ) = ∑ i ∈ Aᶜ, (p.get i : ℝ) := by
      exact_mod_cast hA
    have htot : ∑ i ∈ A, (p.get i : ℝ) + ∑ i ∈ Aᶜ, (p.get i : ℝ) = partSum p := by
      rw [Finset.sum_add_sum_compl, sum_get_real_eq_partSum]
    have hsumA : ∑ i ∈ A, (p.get i : ℝ) = partSum p / 2 := by linarith
    have hsumAc : ∑ i ∈ Aᶜ, (p.get i : ℝ) = partSum p / 2 := by linarith
    have hP_nonneg : 0 ≤ partSum p := by unfold partSum; positivity
    set w : Fin p.length → ℝ := fun i => (p.get i : ℝ)
    have hw : ∀ i, 0 ≤ w i := fun i => by positivity
    let s1A : Fin (openInst p).nA → ℝ := fun i =>
      if i ∈ A then 0 + cum w A i else partSum p + cum w Aᶜ i
    let s2A : Fin (openInst p).nA → ℝ := fun i =>
      if i ∈ A then partSum p + cum w A i else partSum p / 2 + cum w Aᶜ i
    let s1B : Fin (openInst p).nB → ℝ := fun _ => partSum p / 2
    let s2B : Fin (openInst p).nB → ℝ := fun _ => 0
    let s₁ : Fin ((openInst p).nA + (openInst p).nB) → ℝ :=
      fun j => Sum.elim s1A s1B (finSumFinEquiv.symm j)
    let s₂ : Fin ((openInst p).nA + (openInst p).nB) → ℝ :=
      fun j => Sum.elim s2A s2B (finSumFinEquiv.symm j)
    have hs1_inl : ∀ j i, finSumFinEquiv.symm j = Sum.inl i → s₁ j = s1A i := by
      intro j i h; dsimp only [s₁]; rw [h]; rfl
    have hs1_inr : ∀ j k, finSumFinEquiv.symm j = Sum.inr k → s₁ j = partSum p / 2 := by
      intro j k h; dsimp only [s₁]; rw [h]; rfl
    have hs2_inl : ∀ j i, finSumFinEquiv.symm j = Sum.inl i → s₂ j = s2A i := by
      intro j i h; dsimp only [s₂]; rw [h]; rfl
    have hs2_inr : ∀ j k, finSumFinEquiv.symm j = Sum.inr k → s₂ j = 0 := by
      intro j k h; dsimp only [s₂]; rw [h]; rfl
    have hp1_inl : ∀ j i, finSumFinEquiv.symm j = Sum.inl i → (openInst p).p1 j = w i := by
      intro j i h; unfold Instance.p1; rw [h]; rfl
    have hp1_inr : ∀ j k, finSumFinEquiv.symm j = Sum.inr k → (openInst p).p1 j = partSum p / 2 := by
      intro j k h; unfold Instance.p1; rw [h]; rfl
    have hp2_inl : ∀ j i, finSumFinEquiv.symm j = Sum.inl i → (openInst p).p2 j = w i := by
      intro j i h; unfold Instance.p2; rw [h]; rfl
    have hp2_inr : ∀ j k, finSumFinEquiv.symm j = Sum.inr k → (openInst p).p2 j = partSum p / 2 := by
      intro j k h; unfold Instance.p2; rw [h]; rfl
    have hs1A_pos : ∀ i : Fin (openInst p).nA, i ∈ A → s1A i = 0 + cum w A i :=
      fun i hi => if_pos hi
    have hs1A_neg : ∀ i : Fin (openInst p).nA, i ∉ A → s1A i = partSum p + cum w Aᶜ i :=
      fun i hi => if_neg hi
    have hs2A_pos : ∀ i : Fin (openInst p).nA, i ∈ A → s2A i = partSum p + cum w A i :=
      fun i hi => if_pos hi
    have hs2A_neg : ∀ i : Fin (openInst p).nA, i ∉ A → s2A i = partSum p / 2 + cum w Aᶜ i :=
      fun i hi => if_neg hi
    have hs1A_bounds : ∀ i : Fin (openInst p).nA,
        (i ∈ A → 0 ≤ s1A i ∧ s1A i + w i ≤ partSum p / 2) ∧
        (i ∉ A → partSum p ≤ s1A i ∧ s1A i + w i ≤ 3 * partSum p / 2) := by
      intro i
      constructor
      · intro hi
        have h1 := cum_nonneg hw A i
        have h2 := cum_add_le_sum hw hi
        rw [hs1A_pos i hi]
        exact ⟨by linarith, by linarith⟩
      · intro hni
        have hi : i ∈ Aᶜ := Finset.mem_compl.mpr hni
        have h1 := cum_nonneg hw Aᶜ i
        have h2 := cum_add_le_sum hw hi
        rw [hs1A_neg i hni]
        exact ⟨by linarith, by linarith⟩
    have hs2A_bounds : ∀ i : Fin (openInst p).nA,
        (i ∈ A → partSum p ≤ s2A i ∧ s2A i + w i ≤ 3 * partSum p / 2) ∧
        (i ∉ A → partSum p / 2 ≤ s2A i ∧ s2A i + w i ≤ partSum p) := by
      intro i
      constructor
      · intro hi
        have h1 := cum_nonneg hw A i
        have h2 := cum_add_le_sum hw hi
        rw [hs2A_pos i hi]
        exact ⟨by linarith, by linarith⟩
      · intro hni
        have hi : i ∈ Aᶜ := Finset.mem_compl.mpr hni
        have h1 := cum_nonneg hw Aᶜ i
        have h2 := cum_add_le_sum hw hi
        rw [hs2A_neg i hni]
        exact ⟨by linarith, by linarith⟩
    refine ⟨s₁, s₂, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro j
      rcases h : finSumFinEquiv.symm j with i | k
      · rw [hs1_inl j i h]
        by_cases hi : i ∈ A
        · exact (hs1A_bounds i).1 hi |>.1
        · linarith [(hs1A_bounds i).2 hi |>.1]
      · rw [hs1_inr j k h]; linarith
    · intro j
      rcases h : finSumFinEquiv.symm j with i | k
      · rw [hs2_inl j i h]
        by_cases hi : i ∈ A
        · linarith [(hs2A_bounds i).1 hi |>.1]
        · linarith [(hs2A_bounds i).2 hi |>.1]
      · rw [hs2_inr j k h]
    · intro j₁ j₂ hne
      rcases h1 : finSumFinEquiv.symm j₁ with i₁ | k₁ <;>
        rcases h2 : finSumFinEquiv.symm j₂ with i₂ | k₂
      · rw [hs1_inl j₁ i₁ h1, hs1_inl j₂ i₂ h2, hp1_inl j₁ i₁ h1, hp1_inl j₂ i₂ h2]
        have hij : i₁ ≠ i₂ := by
          intro e; apply hne; apply finSumFinEquiv.symm.injective; rw [h1, h2, e]
        by_cases hi1 : i₁ ∈ A <;> by_cases hi2 : i₂ ∈ A
        · rw [hs1A_pos i₁ hi1, hs1A_pos i₂ hi2]
          exact cum_disj hw hi1 hi2 hij 0
        · left; linarith [(hs1A_bounds i₁).1 hi1 |>.2, (hs1A_bounds i₂).2 hi2 |>.1]
        · right; linarith [(hs1A_bounds i₂).1 hi2 |>.2, (hs1A_bounds i₁).2 hi1 |>.1]
        · rw [hs1A_neg i₁ hi1, hs1A_neg i₂ hi2]
          exact cum_disj hw (Finset.mem_compl.mpr hi1) (Finset.mem_compl.mpr hi2) hij (partSum p)
      · rw [hs1_inl j₁ i₁ h1, hs1_inr j₂ k₂ h2, hp1_inl j₁ i₁ h1, hp1_inr j₂ k₂ h2]
        by_cases hi1 : i₁ ∈ A
        · left; linarith [(hs1A_bounds i₁).1 hi1 |>.2]
        · right; linarith [(hs1A_bounds i₁).2 hi1 |>.1]
      · rw [hs1_inr j₁ k₁ h1, hs1_inl j₂ i₂ h2, hp1_inr j₁ k₁ h1, hp1_inl j₂ i₂ h2]
        by_cases hi2 : i₂ ∈ A
        · right; linarith [(hs1A_bounds i₂).1 hi2 |>.2]
        · left; linarith [(hs1A_bounds i₂).2 hi2 |>.1]
      · exfalso; apply hne; apply finSumFinEquiv.symm.injective
        have hk : k₁ = k₂ := Fin.ext (by
          have hlt1 : k₁.val < 1 := k₁.isLt
          have hlt2 : k₂.val < 1 := k₂.isLt
          omega)
        rw [h1, h2, hk]
    · intro j₁ j₂ hne
      rcases h1 : finSumFinEquiv.symm j₁ with i₁ | k₁ <;>
        rcases h2 : finSumFinEquiv.symm j₂ with i₂ | k₂
      · rw [hs2_inl j₁ i₁ h1, hs2_inl j₂ i₂ h2, hp2_inl j₁ i₁ h1, hp2_inl j₂ i₂ h2]
        have hij : i₁ ≠ i₂ := by
          intro e; apply hne; apply finSumFinEquiv.symm.injective; rw [h1, h2, e]
        by_cases hi1 : i₁ ∈ A <;> by_cases hi2 : i₂ ∈ A
        · rw [hs2A_pos i₁ hi1, hs2A_pos i₂ hi2]
          exact cum_disj hw hi1 hi2 hij (partSum p)
        · right; linarith [(hs2A_bounds i₂).2 hi2 |>.2, (hs2A_bounds i₁).1 hi1 |>.1]
        · left; linarith [(hs2A_bounds i₁).2 hi1 |>.2, (hs2A_bounds i₂).1 hi2 |>.1]
        · rw [hs2A_neg i₁ hi1, hs2A_neg i₂ hi2]
          exact cum_disj hw (Finset.mem_compl.mpr hi1) (Finset.mem_compl.mpr hi2) hij (partSum p / 2)
      · rw [hs2_inl j₁ i₁ h1, hs2_inr j₂ k₂ h2, hp2_inl j₁ i₁ h1, hp2_inr j₂ k₂ h2]
        by_cases hi1 : i₁ ∈ A
        · right; linarith [(hs2A_bounds i₁).1 hi1 |>.1]
        · right; linarith [(hs2A_bounds i₁).2 hi1 |>.1]
      · rw [hs2_inr j₁ k₁ h1, hs2_inl j₂ i₂ h2, hp2_inr j₁ k₁ h1, hp2_inl j₂ i₂ h2]
        by_cases hi2 : i₂ ∈ A
        · left; linarith [(hs2A_bounds i₂).1 hi2 |>.1]
        · left; linarith [(hs2A_bounds i₂).2 hi2 |>.1]
      · exfalso; apply hne; apply finSumFinEquiv.symm.injective
        have hk : k₁ = k₂ := Fin.ext (by
          have hlt1 : k₁.val < 1 := k₁.isLt
          have hlt2 : k₂.val < 1 := k₂.isLt
          omega)
        rw [h1, h2, hk]
    · intro j
      rcases h : finSumFinEquiv.symm j with i | k
      · rw [hs1_inl j i h, hs2_inl j i h, hp1_inl j i h, hp2_inl j i h]
        by_cases hi : i ∈ A
        · left; linarith [(hs1A_bounds i).1 hi |>.2, (hs2A_bounds i).1 hi |>.1]
        · right; linarith [(hs1A_bounds i).2 hi |>.1, (hs2A_bounds i).2 hi |>.2]
      · rw [hs1_inr j k h, hs2_inr j k h, hp1_inr j k h, hp2_inr j k h]
        right; linarith
    · intro i
      have ha : finSumFinEquiv.symm ((openInst p).aJob i) = Sum.inl i :=
        finSumFinEquiv_symm_apply_castAdd i
      rw [hs1_inl _ i ha, hs2_inl _ i ha]
      change s1A i + w i ≤ 3 * partSum p / 2 ∧ s2A i + w i ≤ 3 * partSum p / 2
      by_cases hi : i ∈ A
      · exact ⟨by linarith [(hs1A_bounds i).1 hi |>.2], by linarith [(hs2A_bounds i).1 hi |>.2]⟩
      · exact ⟨by linarith [(hs1A_bounds i).2 hi |>.2], by linarith [(hs2A_bounds i).2 hi |>.2]⟩
    · intro k
      have hb : finSumFinEquiv.symm ((openInst p).bJob k) = Sum.inr k :=
        finSumFinEquiv_symm_apply_natAdd k
      rw [hs1_inr _ k hb, hs2_inr _ k hb]
      change partSum p / 2 + partSum p / 2 ≤ partSum p ∧ 0 + partSum p / 2 ≤ partSum p
      exact ⟨by linarith, by linarith⟩
  · rintro ⟨s₁, s₂, hfeas, hA, hB⟩
    rcases open_bjob_starts p s₁ s₂ hfeas hB with ⟨_, hs2_half⟩ | ⟨_, hs1_half⟩
    · exact partition_of_b_at_half p s₂ hfeas.2.1 hfeas.2.2.2.1 hs2_half (fun i => (hA i).2)
    · exact partition_of_b_at_half p s₁ hfeas.1 hfeas.2.2.1 hs1_half (fun i => (hA i).1)
