-- Prove2me | solution 1 for VehicleSharePricing.MultiNet.component_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:52:34.824469+00:00
-- url     : https://prove2.me/submissions/3c583f16-7480-48ab-8642-3f5ae9f97963

import Mathlib
import Definitions.Def_VehicleSharePricing_MultiNet_Model

set_option autoImplicit false
open VehicleSharePricing.MultiNet Finset

section
variable {L ι : Type*} [Fintype L] [DecidableEq L] [Nonempty L] [Fintype ι] [DecidableEq ι]
  {Λ μ : L → L → ℝ} {I : L → L → ℝ → ℝ} {Δ : ℝ} {K : ℕ} {q : L → L → ℝ} {r : L → ℝ}
  {comp : L → ι}

lemma lam_q_nonneg (h : SplitStaticSetting Λ μ I Δ K q r comp) (i j : L) :
    0 ≤ Λ i j * q i j := by
  rcases (h.standing.demand_nonneg i j).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · have := h.optimal.1.2.2 i j h0
    exact mul_nonneg h0.le this.1

lemma lam_q_pos_comp (h : SplitStaticSetting Λ μ I Δ K q r comp) (i j : L)
    (hp : 0 < Λ i j * q i j) : comp i = comp j := h.split.2.1 i j hp

lemma lam_q_eq_zero (h : SplitStaticSetting Λ μ I Δ K q r comp) (i j : L)
    (hne : comp i ≠ comp j) : Λ i j * q i j = 0 := by
  rcases (lam_q_nonneg h i j).eq_or_lt with h0 | h0
  · exact h0.symm
  · exact absurd (lam_q_pos_comp h i j h0) hne

lemma rewardS_nonneg' (h : SplitStaticSetting Λ μ I Δ K q r comp) : 0 ≤ rewardS Λ I q := by
  have hΔ : 0 ≤ Δ := le_trans (Nat.cast_nonneg K) h.budget_ge
  have h0 : Feasible Λ μ Δ (fun _ _ => (0 : ℝ)) := by
    refine ⟨fun i => by simp, ?_, fun i j _ => by simp⟩
    simpa using hΔ
  have := h.optimal.2 _ h0
  simpa [rewardS] using this

lemma classSum_nonneg (h : SplitStaticSetting Λ μ I Δ K q r comp) (c : ι) :
    0 ≤ ∑ p ∈ classArcs Λ comp c, q p.1 p.2 * Λ p.1 p.2 * I p.1 p.2 (q p.1 p.2) := by
  classical
  set q' : L → L → ℝ := fun i j => if comp i = c then 0 else q i j with hq'
  have hfeas : Feasible Λ μ Δ q' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases hi : comp i = c
      · have e1 : ∑ j, Λ i j * q' i j = 0 := by simp [hq', hi]
        have e2 : ∑ j, Λ j i * q' j i = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          by_cases hj : comp j = c
          · simp [hq', hj]
          · have : comp j ≠ comp i := by rw [hi]; exact hj
            have := lam_q_eq_zero h j i this
            simp [hq', hj, this]
        rw [e1, e2]
      · have e1 : ∑ j, Λ i j * q' i j = ∑ j, Λ i j * q i j := by simp [hq', hi]
        have e2 : ∑ j, Λ j i * q' j i = ∑ j, Λ j i * q j i := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : comp j = c
          · have : comp j ≠ comp i := by rw [hj]; exact fun e => hi e.symm
            have := lam_q_eq_zero h j i this
            simp [hq', hj, this]
          · simp [hq', hj]
        rw [e1, e2]; exact h.optimal.1.1 i
    · refine le_trans ?_ h.optimal.1.2.1
      apply Finset.sum_le_sum
      intro p hp
      have hp' : 0 < Λ p.1 p.2 := (Finset.mem_filter.1 hp).2
      have hμ := h.standing.rate_pos _ _ hp'
      have hq0 := (h.optimal.1.2.2 _ _ hp').1
      by_cases hc : comp p.1 = c
      · simp only [hq', hc, if_true]
        have : 0 ≤ Λ p.1 p.2 * q p.1 p.2 / μ p.1 p.2 := div_nonneg (mul_nonneg hp'.le hq0) hμ.le
        simpa using this
      · simp [hq', hc]
    · intro i j hij
      have := h.optimal.1.2.2 i j hij
      by_cases hc : comp i = c
      · simp [hq', hc]
      · simpa [hq', hc] using this
  have hle := h.optimal.2 q' hfeas
  have key : rewardS Λ I q = rewardS Λ I q' +
      ∑ p ∈ classArcs Λ comp c, q p.1 p.2 * Λ p.1 p.2 * I p.1 p.2 (q p.1 p.2) := by
    unfold rewardS classArcs
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : 0 < Λ p.1 p.2 := (Finset.mem_filter.1 hp).2
    by_cases hc : comp p.1 = c
    · by_cases hc2 : comp p.2 = c
      · rw [if_pos ⟨hc, hc2⟩]
        simp only [hq', hc, if_true]
        ring
      · have hz := lam_q_eq_zero h p.1 p.2 (by rw [hc]; exact fun e => hc2 e.symm)
        rw [if_neg (by tauto)]
        simp only [hq', hc, if_true]
        have : Λ p.1 p.2 * q p.1 p.2 * I p.1 p.2 (q p.1 p.2) = 0 := by rw [hz, zero_mul]
        rw [this]; ring
    · rw [if_neg (by tauto)]
      simp only [hq', hc, if_false]
      ring
  linarith

lemma weight_nonneg' {S T : Type*} [Fintype S] [Fintype T] (a : S → ℝ) (b : T → ℝ)
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ t, 0 ≤ b t) (x : S ⊕ T → ℕ) : 0 ≤ weight a b x := by
  unfold weight
  refine mul_nonneg (Finset.prod_nonneg fun s _ => pow_nonneg (ha s) _)
    (Finset.prod_nonneg fun t _ => ?_)
  exact div_nonneg (pow_nonneg (hb t) _) (Nat.cast_nonneg _)

lemma availability_mem' {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (a : S → ℝ) (b : T → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ t, 0 ≤ b t) (K : ℕ) (s : S) :
    0 ≤ availability a b K s ∧ availability a b K s ≤ 1 := by
  unfold availability normConst
  have hsub : (∑ x ∈ (states S T K).filter (fun x => 1 ≤ x (Sum.inl s)), weight a b x) ≤
      ∑ x ∈ states S T K, weight a b x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => weight_nonneg' a b ha hb x)
  have hnum : 0 ≤ ∑ x ∈ (states S T K).filter (fun x => 1 ≤ x (Sum.inl s)), weight a b x :=
    Finset.sum_nonneg fun x _ => weight_nonneg' a b ha hb x
  refine ⟨div_nonneg hnum (le_trans hnum hsub), ?_⟩
  rcases (le_trans hnum hsub).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · rw [div_le_one h0]; exact hsub

lemma classAvail_mem (h : SplitStaticSetting Λ μ I Δ K q r comp) (c : ι) (Kc : ℕ)
    (i : ClassLoc comp c) :
    0 ≤ classAvail Λ μ q r comp c Kc i ∧ classAvail Λ μ q r comp c Kc i ≤ 1 := by
  have hpick : ∀ j, 0 ≤ pickupRate Λ q j := fun j =>
    Finset.sum_nonneg fun k _ => lam_q_nonneg h j k
  unfold classAvail
  apply availability_mem'
  · intro s
    exact div_nonneg (h.r_pos s.1).le (hpick s.1)
  · intro t
    have hμ := h.standing.rate_pos _ _ t.2.2.2
    exact div_nonneg (mul_nonneg (h.r_pos _).le (lam_q_nonneg h _ _))
      (mul_nonneg (hpick _) hμ.le)

lemma classWorkload_nonneg (h : SplitStaticSetting Λ μ I Δ K q r comp) (c : ι) :
    0 ≤ classWorkload Λ μ q comp c := by
  unfold classWorkload
  apply Finset.sum_nonneg
  intro p hp
  have hp' : 0 < Λ p.1 p.2 := by
    have := (Finset.mem_filter.1 hp).1
    exact (Finset.mem_filter.1 this).2
  have hμ := h.standing.rate_pos _ _ hp'
  have hq0 := (h.optimal.1.2.2 _ _ hp').1
  positivity

end

theorem solution {L ι : Type*} [Fintype L] [DecidableEq L] [Nonempty L] [Fintype ι] [DecidableEq ι]
    (Λ μ : L → L → ℝ) (I : L → L → ℝ → ℝ) (Δ : ℝ) (K : ℕ) (q : L → L → ℝ) (r : L → ℝ)
    (comp : L → ι) (h : SplitStaticSetting Λ μ I Δ K q r comp)
    (c : ι) (i : ClassLoc comp c) (Kc : ℕ) (hKc0 : 0 < Kc) (hKcK : Kc ≤ K) :
    classWeight Λ q I comp c * (Kc : ℝ) /
        ((classSize comp c : ℝ) + (Kc : ℝ) - 1 + classWorkload Λ μ q comp c) ≤
      classWeight Λ q I comp c * (Kc : ℝ) /
        ((classSize comp c : ℝ) + (Kc : ℝ) - 1 +
          classWorkload Λ μ q comp c * (1 - classAvail Λ μ q r comp c (Kc - 1) i)) := by
  have hw : 0 ≤ classWeight Λ q I comp c :=
    div_nonneg (classSum_nonneg h c) (rewardS_nonneg' h)
  obtain ⟨ha0, ha1⟩ := classAvail_mem h c (Kc - 1) i
  have hM := classWorkload_nonneg h c
  have hN : (1 : ℝ) ≤ (classSize comp c : ℝ) := by
    have : 0 < classSize comp c := Fintype.card_pos_iff.2 ⟨i⟩
    exact_mod_cast this
  have hK1 : (1 : ℝ) ≤ (Kc : ℝ) := by exact_mod_cast hKc0
  have hden : 0 < (classSize comp c : ℝ) + (Kc : ℝ) - 1 +
      classWorkload Λ μ q comp c * (1 - classAvail Λ μ q r comp c (Kc - 1) i) := by
    have : 0 ≤ classWorkload Λ μ q comp c * (1 - classAvail Λ μ q r comp c (Kc - 1) i) :=
      mul_nonneg hM (by linarith)
    linarith
  apply div_le_div_of_nonneg_left (by positivity) hden
  have : 0 ≤ classWorkload Λ μ q comp c * classAvail Λ μ q r comp c (Kc - 1) i :=
    mul_nonneg hM ha0
  nlinarith
