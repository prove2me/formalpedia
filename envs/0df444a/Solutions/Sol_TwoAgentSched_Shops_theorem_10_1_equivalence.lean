-- Prove2me | solution 1 for TwoAgentSched.Shops.theorem_10_1_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:14:18.057625+00:00
-- url     : https://prove2.me/submissions/5fb883aa-2a9c-42bd-bd75-c704659e384a

import Mathlib
import Definitions.Def_TwoAgentSched_Shops_Construction
import Theorems.Thm_TwoAgentSched_Shops_flow_bjob_latest_start

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

private lemma eps_pos (p : List ℕ) : 0 < eps p := by
  unfold eps; positivity

private lemma k_mul_eps_lt_one (p : List ℕ) : (p.length : ℝ) * eps p < 1 := by
  unfold eps
  rw [mul_one_div, div_lt_iff₀ (by positivity)]
  linarith

private lemma eps_le_one (p : List ℕ) : eps p ≤ 1 := by
  unfold eps
  rw [div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ (p.length : ℝ) := Nat.cast_nonneg p.length
  linarith

private lemma pB1_nonneg (p : List ℕ) (hrange : 2 ≤ p.sum ∨ p.length ≤ 1) :
    0 ≤ partSum p / 2 - ((p.length : ℝ) - 1) * eps p := by
  have heps : 0 < eps p := eps_pos p
  rcases hrange with h2 | h1
  · have hP : (2 : ℝ) ≤ partSum p := by unfold partSum; exact_mod_cast h2
    have hk : (p.length : ℝ) * eps p < 1 := k_mul_eps_lt_one p
    nlinarith
  · have hk : (p.length : ℝ) ≤ 1 := by exact_mod_cast h1
    have hP : 0 ≤ partSum p := by unfold partSum; positivity
    nlinarith

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

open Classical in
theorem solution (p : List ℕ) (heven : Even p.sum)
    (hrange : 2 ≤ p.sum ∨ p.length ≤ 1) :
    PartitionYes p ↔ (flowInst p).FlowYes (flowQA p) (flowQB p) := by
  constructor
  · rintro ⟨A₀, hA₀⟩
    set A := A₀.filter (fun i : Fin p.length => 1 ≤ p.get i)
    have hA_eq : ∑ i ∈ A, p.get i = ∑ i ∈ A₀, p.get i := by
      refine Finset.sum_subset (Finset.filter_subset _ _) (fun i hi hni => ?_)
      have : ¬ (1 ≤ p.get i) := fun h => hni (Finset.mem_filter.mpr ⟨hi, h⟩)
      omega
    have hA : ∑ i ∈ A, p.get i = ∑ i ∈ Aᶜ, p.get i := by
      have h1 := Finset.sum_add_sum_compl A (fun i : Fin p.length => p.get i)
      have h2 := Finset.sum_add_sum_compl A₀ (fun i : Fin p.length => p.get i)
      omega
    have hA_real : ∑ i ∈ A, (p.get i : ℝ) = ∑ i ∈ Aᶜ, (p.get i : ℝ) := by
      exact_mod_cast hA
    have htot : ∑ i ∈ A, (p.get i : ℝ) + ∑ i ∈ Aᶜ, (p.get i : ℝ) = partSum p := by
      rw [Finset.sum_add_sum_compl, sum_get_real_eq_partSum]
    have hsumA : ∑ i ∈ A, (p.get i : ℝ) = partSum p / 2 := by linarith
    have hsumAc : ∑ i ∈ Aᶜ, (p.get i : ℝ) = partSum p / 2 := by linarith
    have hP_nonneg : 0 ≤ partSum p := by unfold partSum; positivity
    have heps_pos : 0 < eps p := eps_pos p
    have heps_le_one : eps p ≤ 1 := eps_le_one p
    have hpB1_nonneg : 0 ≤ partSum p / 2 - ((p.length : ℝ) - 1) * eps p := pB1_nonneg p hrange
    set w : Fin p.length → ℝ := fun i => (p.get i : ℝ)
    set e : Fin p.length → ℝ := fun _ => eps p
    have hw : ∀ i, 0 ≤ w i := fun i => by positivity
    have he : ∀ i, 0 ≤ e i := fun _ => le_of_lt heps_pos
    have hsum_e_A : ∑ j ∈ A, e j = (A.card : ℝ) * eps p := by
      simp [e]
    have hsum_e_Ac : ∑ j ∈ Aᶜ, e j = (Aᶜ.card : ℝ) * eps p := by
      simp [e]
    have hcard_tot : (A.card : ℝ) + (Aᶜ.card : ℝ) = (p.length : ℝ) := by
      have : A.card + Aᶜ.card = p.length := by
        simpa using Finset.card_add_card_compl A
      exact_mod_cast this
    let s1A : Fin (flowInst p).nA → ℝ := fun i =>
      if i ∈ A then 0 + cum e A i else (A.card : ℝ) * eps p + cum e Aᶜ i
    let s2A : Fin (flowInst p).nA → ℝ := fun i =>
      if i ∈ A then eps p + cum w A i else partSum p + eps p + cum w Aᶜ i
    let s1B : Fin (flowInst p).nB → ℝ := fun _ => (p.length : ℝ) * eps p
    let s2B : Fin (flowInst p).nB → ℝ := fun _ => partSum p / 2 + eps p
    let s₁ : Fin ((flowInst p).nA + (flowInst p).nB) → ℝ :=
      fun j => Sum.elim s1A s1B (finSumFinEquiv.symm j)
    let s₂ : Fin ((flowInst p).nA + (flowInst p).nB) → ℝ :=
      fun j => Sum.elim s2A s2B (finSumFinEquiv.symm j)
    have hs1_inl : ∀ j i, finSumFinEquiv.symm j = Sum.inl i → s₁ j = s1A i := by
      intro j i h; dsimp only [s₁]; rw [h]; rfl
    have hs1_inr : ∀ j k, finSumFinEquiv.symm j = Sum.inr k → s₁ j = (p.length : ℝ) * eps p := by
      intro j k h; dsimp only [s₁]; rw [h]; rfl
    have hs2_inl : ∀ j i, finSumFinEquiv.symm j = Sum.inl i → s₂ j = s2A i := by
      intro j i h; dsimp only [s₂]; rw [h]; rfl
    have hs2_inr : ∀ j k, finSumFinEquiv.symm j = Sum.inr k → s₂ j = partSum p / 2 + eps p := by
      intro j k h; dsimp only [s₂]; rw [h]; rfl
    have hp1_inl : ∀ j i, finSumFinEquiv.symm j = Sum.inl i → (flowInst p).p1 j = eps p := by
      intro j i h; unfold Instance.p1; rw [h]; rfl
    have hp1_inr : ∀ j k, finSumFinEquiv.symm j = Sum.inr k →
        (flowInst p).p1 j = partSum p / 2 - ((p.length : ℝ) - 1) * eps p := by
      intro j k h; unfold Instance.p1; rw [h]; rfl
    have hp2_inl : ∀ j i, finSumFinEquiv.symm j = Sum.inl i → (flowInst p).p2 j = w i := by
      intro j i h; unfold Instance.p2; rw [h]; rfl
    have hp2_inr : ∀ j k, finSumFinEquiv.symm j = Sum.inr k → (flowInst p).p2 j = partSum p / 2 := by
      intro j k h; unfold Instance.p2; rw [h]; rfl
    have hs1A_pos : ∀ i : Fin (flowInst p).nA, i ∈ A → s1A i = 0 + cum e A i :=
      fun i hi => if_pos hi
    have hs1A_neg : ∀ i : Fin (flowInst p).nA, i ∉ A → s1A i = (A.card : ℝ) * eps p + cum e Aᶜ i :=
      fun i hi => if_neg hi
    have hs2A_pos : ∀ i : Fin (flowInst p).nA, i ∈ A → s2A i = eps p + cum w A i :=
      fun i hi => if_pos hi
    have hs2A_neg : ∀ i : Fin (flowInst p).nA, i ∉ A → s2A i = partSum p + eps p + cum w Aᶜ i :=
      fun i hi => if_neg hi
    have hs1A_bounds : ∀ i : Fin (flowInst p).nA,
        (i ∈ A → 0 ≤ s1A i ∧ s1A i + eps p ≤ (A.card : ℝ) * eps p) ∧
        (i ∉ A → (A.card : ℝ) * eps p ≤ s1A i ∧ s1A i + eps p ≤ (p.length : ℝ) * eps p) := by
      intro i
      constructor
      · intro hi
        have h1 := cum_nonneg he A i
        have h2 := cum_add_le_sum he hi
        rw [hs1A_pos i hi]
        exact ⟨by linarith, by linarith⟩
      · intro hni
        have hi : i ∈ Aᶜ := Finset.mem_compl.mpr hni
        have h1 := cum_nonneg he Aᶜ i
        have h2 := cum_add_le_sum he hi
        have hA_nonneg : 0 ≤ (A.card : ℝ) * eps p := by positivity
        rw [hs1A_neg i hni]
        exact ⟨by linarith, by nlinarith⟩
    have hs2A_bounds : ∀ i : Fin (flowInst p).nA,
        (i ∈ A → eps p ≤ s2A i ∧ s2A i + w i ≤ partSum p / 2 + eps p) ∧
        (i ∉ A → partSum p + eps p ≤ s2A i ∧ s2A i + w i ≤ 3 * partSum p / 2 + eps p) := by
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
    refine ⟨s₁, s₂, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro j
      rcases h : finSumFinEquiv.symm j with i | k
      · rw [hs1_inl j i h]
        by_cases hi : i ∈ A
        · exact (hs1A_bounds i).1 hi |>.1
        · have : 0 ≤ (A.card : ℝ) * eps p := by positivity
          linarith [(hs1A_bounds i).2 hi |>.1]
      · rw [hs1_inr j k h]; positivity
    · intro j₁ j₂ hne
      rcases h1 : finSumFinEquiv.symm j₁ with i₁ | k₁ <;>
        rcases h2 : finSumFinEquiv.symm j₂ with i₂ | k₂
      · rw [hs1_inl j₁ i₁ h1, hs1_inl j₂ i₂ h2, hp1_inl j₁ i₁ h1, hp1_inl j₂ i₂ h2]
        have hij : i₁ ≠ i₂ := by
          intro e; apply hne; apply finSumFinEquiv.symm.injective; rw [h1, h2, e]
        by_cases hi1 : i₁ ∈ A <;> by_cases hi2 : i₂ ∈ A
        · rw [hs1A_pos i₁ hi1, hs1A_pos i₂ hi2]
          exact cum_disj he hi1 hi2 hij 0
        · left; linarith [(hs1A_bounds i₁).1 hi1 |>.2, (hs1A_bounds i₂).2 hi2 |>.1]
        · right; linarith [(hs1A_bounds i₂).1 hi2 |>.2, (hs1A_bounds i₁).2 hi1 |>.1]
        · rw [hs1A_neg i₁ hi1, hs1A_neg i₂ hi2]
          exact cum_disj he (Finset.mem_compl.mpr hi1) (Finset.mem_compl.mpr hi2) hij ((A.card : ℝ) * eps p)
      · rw [hs1_inl j₁ i₁ h1, hs1_inr j₂ k₂ h2, hp1_inl j₁ i₁ h1, hp1_inr j₂ k₂ h2]
        have hAc_nonneg : 0 ≤ (Aᶜ.card : ℝ) * eps p := by positivity
        by_cases hi1 : i₁ ∈ A
        · left; nlinarith [(hs1A_bounds i₁).1 hi1 |>.2]
        · left; linarith [(hs1A_bounds i₁).2 hi1 |>.2]
      · rw [hs1_inr j₁ k₁ h1, hs1_inl j₂ i₂ h2, hp1_inr j₁ k₁ h1, hp1_inl j₂ i₂ h2]
        have hAc_nonneg : 0 ≤ (Aᶜ.card : ℝ) * eps p := by positivity
        by_cases hi2 : i₂ ∈ A
        · right; nlinarith [(hs1A_bounds i₂).1 hi2 |>.2]
        · right; linarith [(hs1A_bounds i₂).2 hi2 |>.2]
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
          exact cum_disj hw hi1 hi2 hij (eps p)
        · left; linarith [(hs2A_bounds i₁).1 hi1 |>.2, (hs2A_bounds i₂).2 hi2 |>.1]
        · right; linarith [(hs2A_bounds i₂).1 hi2 |>.2, (hs2A_bounds i₁).2 hi1 |>.1]
        · rw [hs2A_neg i₁ hi1, hs2A_neg i₂ hi2]
          exact cum_disj hw (Finset.mem_compl.mpr hi1) (Finset.mem_compl.mpr hi2) hij (partSum p + eps p)
      · rw [hs2_inl j₁ i₁ h1, hs2_inr j₂ k₂ h2, hp2_inl j₁ i₁ h1, hp2_inr j₂ k₂ h2]
        by_cases hi1 : i₁ ∈ A
        · left; linarith [(hs2A_bounds i₁).1 hi1 |>.2]
        · right; linarith [(hs2A_bounds i₁).2 hi1 |>.1]
      · rw [hs2_inr j₁ k₁ h1, hs2_inl j₂ i₂ h2, hp2_inr j₁ k₁ h1, hp2_inl j₂ i₂ h2]
        by_cases hi2 : i₂ ∈ A
        · right; linarith [(hs2A_bounds i₂).1 hi2 |>.2]
        · left; linarith [(hs2A_bounds i₂).2 hi2 |>.1]
      · exfalso; apply hne; apply finSumFinEquiv.symm.injective
        have hk : k₁ = k₂ := Fin.ext (by
          have hlt1 : k₁.val < 1 := k₁.isLt
          have hlt2 : k₂.val < 1 := k₂.isLt
          omega)
        rw [h1, h2, hk]
    · intro j
      rcases h : finSumFinEquiv.symm j with i | k
      · rw [hs1_inl j i h, hs2_inl j i h, hp1_inl j i h]
        by_cases hi : i ∈ A
        · rw [hs1A_pos i hi, hs2A_pos i hi]
          have hcum_le : cum e A i ≤ cum w A i := by
            unfold cum
            refine Finset.sum_le_sum (fun x hx => ?_)
            have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
            have hx1 : 1 ≤ p.get x := (Finset.mem_filter.mp hxA).2
            have hx1_real : (1 : ℝ) ≤ w x := by
              change (1 : ℝ) ≤ (p.get x : ℝ)
              exact_mod_cast hx1
            linarith
          linarith
        · linarith [(hs1A_bounds i).2 hi |>.2, (hs2A_bounds i).2 hi |>.1]
      · rw [hs1_inr j k h, hs2_inr j k h, hp1_inr j k h]
        linarith
    · intro i
      have ha : finSumFinEquiv.symm ((flowInst p).aJob i) = Sum.inl i :=
        finSumFinEquiv_symm_apply_castAdd i
      rw [hs1_inl _ i ha, hs2_inl _ i ha]
      change s1A i + eps p ≤ 3 * partSum p / 2 + eps p ∧ s2A i + w i ≤ 3 * partSum p / 2 + eps p
      have hAc_nonneg : 0 ≤ (Aᶜ.card : ℝ) * eps p := by positivity
      by_cases hi : i ∈ A
      · exact ⟨by nlinarith [(hs1A_bounds i).1 hi |>.2], by linarith [(hs2A_bounds i).1 hi |>.2]⟩
      · exact ⟨by linarith [(hs1A_bounds i).2 hi |>.2], by linarith [(hs2A_bounds i).2 hi |>.2]⟩
    · intro k
      have hb : finSumFinEquiv.symm ((flowInst p).bJob k) = Sum.inr k :=
        finSumFinEquiv_symm_apply_natAdd k
      rw [hs1_inr _ k hb, hs2_inr _ k hb]
      change (p.length : ℝ) * eps p + (partSum p / 2 - ((p.length : ℝ) - 1) * eps p) ≤ partSum p + eps p ∧
        (partSum p / 2 + eps p) + partSum p / 2 ≤ partSum p + eps p
      exact ⟨by linarith, by linarith⟩
  · rintro ⟨s₁, s₂, hfeas, hA, hB⟩
    obtain ⟨hs2B, hsumS⟩ := flow_bjob_latest_start p s₁ s₂ hfeas hB
    set S := Finset.univ.filter (fun i : Fin p.length => s₂ (flowA p i) < s₂ (flowB p))
    set T := Sᶜ.filter (fun i : Fin p.length => 1 ≤ p.get i)
    have hb : finSumFinEquiv.symm (flowB p) = Sum.inr ⟨0, Nat.one_pos⟩ :=
      finSumFinEquiv_symm_apply_natAdd ⟨0, Nat.one_pos⟩
    have hpB1 : (flowInst p).p1 (flowB p) = partSum p / 2 - ((p.length : ℝ) - 1) * eps p := by
      unfold Instance.p1; rw [hb]; rfl
    have hpB2 : (flowInst p).p2 (flowB p) = partSum p / 2 := by
      unfold Instance.p2; rw [hb]; rfl
    have ha : ∀ i : Fin p.length, finSumFinEquiv.symm (flowA p i) = Sum.inl i :=
      fun i => finSumFinEquiv_symm_apply_castAdd i
    have hpA2 : ∀ i : Fin p.length, (flowInst p).p2 (flowA p i) = (p.get i : ℝ) := by
      intro i; unfold Instance.p2; rw [ha i]; rfl
    have ha_inj : Function.Injective (flowA p) := by
      intro i j hij
      have := congrArg finSumFinEquiv.symm hij
      rw [ha i, ha j] at this
      exact Sum.inl_injective this
    have ha_ne_B : ∀ i : Fin p.length, flowA p i ≠ flowB p := by
      intro i h
      have := congrArg finSumFinEquiv.symm h
      rw [ha i, hb] at this
      nomatch this
    have hs1B_nonneg : 0 ≤ s₁ (flowB p) := hfeas.1 (flowB p)
    have hs12B : s₁ (flowB p) + (partSum p / 2 - ((p.length : ℝ) - 1) * eps p) ≤ s₂ (flowB p) := by
      have := hfeas.2.2.2 (flowB p)
      rwa [hpB1] at this
    have hP_nonneg : 0 ≤ partSum p := by unfold partSum; positivity
    have heps_pos : 0 < eps p := eps_pos p
    have hk_eps_nonneg : 0 ≤ (p.length : ℝ) * eps p := by positivity
    have hsumT : ∑ i ∈ T, (p.get i : ℝ) ≤ partSum p / 2 + (p.length : ℝ) * eps p := by
      have := nonoverlap_sum_le (fun i : Fin p.length => s₂ (flowA p i))
        (fun i : Fin p.length => (p.get i : ℝ)) (fun i => by positivity)
        (fun i j hij => by
          have := hfeas.2.2.1 (flowA p i) (flowA p j) (fun e => hij (ha_inj e))
          rwa [hpA2 i, hpA2 j] at this)
        T.card T rfl (partSum p - ((p.length : ℝ) - 1) * eps p) (3 * partSum p / 2 + eps p)
        (by linarith)
        (fun i hi => by
          obtain ⟨hiSc, hi1⟩ := Finset.mem_filter.mp hi
          have hnot_lt : ¬ (s₂ (flowA p i) < s₂ (flowB p)) := by
            simpa [S] using hiSc
          have hpos : (1 : ℝ) ≤ (p.get i : ℝ) := by exact_mod_cast hi1
          have hdisjB := hfeas.2.2.1 (flowA p i) (flowB p) (ha_ne_B i)
          rw [hpA2 i, hpB2] at hdisjB
          have hAi_end : s₂ (flowA p i) + (p.get i : ℝ) ≤ 3 * partSum p / 2 + eps p := (hA i).2
          rcases hdisjB with h1 | h2
          · exfalso; linarith
          · exact ⟨by linarith, hAi_end⟩)
      linarith
    have hT_eq_Sc : ∑ i ∈ T, p.get i = ∑ i ∈ Sᶜ, p.get i := by
      refine Finset.sum_subset (Finset.filter_subset _ _) (fun i hi hni => ?_)
      have : ¬ (1 ≤ p.get i) := fun h => hni (Finset.mem_filter.mpr ⟨hi, h⟩)
      omega
    have hSc_lt : ∑ i ∈ Sᶜ, (p.get i : ℝ) < partSum p / 2 + 1 := by
      have hcast : ∑ i ∈ T, (p.get i : ℝ) = ∑ i ∈ Sᶜ, (p.get i : ℝ) := by
        exact_mod_cast hT_eq_Sc
      have hk := k_mul_eps_lt_one p
      linarith
    obtain ⟨m, hm⟩ := heven
    have hpart_m : partSum p / 2 = (m : ℝ) := by
      unfold partSum
      rw [hm]
      push_cast
      ring
    have hS_nat : ∑ i ∈ S, p.get i ≤ m := by
      have : (∑ i ∈ S, p.get i : ℝ) ≤ (m : ℝ) := by
        simpa [hpart_m] using hsumS
      exact_mod_cast this
    have hSc_nat : ∑ i ∈ Sᶜ, p.get i < m + 1 := by
      have : (∑ i ∈ Sᶜ, p.get i : ℝ) < (m + 1 : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have htot_nat : ∑ i ∈ S, p.get i + ∑ i ∈ Sᶜ, p.get i = m + m := by
      rw [Finset.sum_add_sum_compl, sum_get_eq_sum, hm]
    refine ⟨S, ?_⟩
    omega
