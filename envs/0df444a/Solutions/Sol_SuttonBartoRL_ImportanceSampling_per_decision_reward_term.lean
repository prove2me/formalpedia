-- Prove2me | solution 1 for SuttonBartoRL.ImportanceSampling.per_decision_reward_term
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T20:24:33.265422+00:00
-- url     : https://prove2.me/submissions/dbad2591-a812-4f9a-9992-132cc783d310

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_Episodes

open SuttonBartoRL.ImportanceSampling Finset
set_option linter.unusedSectionVars false

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

def econsX {M : MDP S A} {n : ℕ} (s : S) (a : A) (r : M.R) (e : Episode M n) :
    Episode M (n + 1) :=
  (Fin.cons s e.1, Fin.cons a e.2.1, Fin.cons r e.2.2)

def econsEquivX (M : MDP S A) (n : ℕ) : S × A × M.R × Episode M n ≃ Episode M (n + 1) where
  toFun x := econsX x.1 x.2.1 x.2.2.1 x.2.2.2
  invFun e := (e.1 0, e.2.1 0, e.2.2 0, (Fin.tail e.1, Fin.tail e.2.1, Fin.tail e.2.2))
  left_inv x := by
    obtain ⟨s, a, r, f, g, h⟩ := x
    simp [econsX]
  right_inv e := by
    obtain ⟨f, g, h⟩ := e
    simp [econsX]

theorem sum_succX (M : MDP S A) (n : ℕ) (F : Episode M (n + 1) → ℝ) :
    ∑ e, F e = ∑ s0 : S, ∑ a : A, ∑ r : M.R, ∑ e' : Episode M n, F (econsX s0 a r e') := by
  rw [← (econsEquivX M n).sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

theorem epconsX (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    {n : ℕ} (s0 : S) (a : A) (r : M.R) (e' : Episode M n) :
    episodeProb M term μ s (econsX s0 a r e') =
      if s0 = s ∧ s0 ∉ term then
        μ.prob s0 a * M.p s0 a (e'.1 0) r * episodeProb M term μ (e'.1 0) e'
      else 0 := by
  unfold episodeProb econsX Episode.states Episode.actions
  simp only [Fin.cons_zero, Fin.prod_univ_succ, Fin.castSucc_zero,
    Fin.cons_succ, Fin.castSucc_succ, Fin.forall_fin_succ, ← Fin.succ_last]
  by_cases h1 : s0 = s
  · subst h1
    by_cases h2 : s0 ∈ term <;> simp [h2]
  · simp [h1]


theorem ep_ne_zeroX (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A)
    (s' : S) {n : ℕ} (e' : Episode M n) (h : e'.1 0 ≠ s') :
    episodeProb M term μ s' e' = 0 := by
  unfold episodeProb
  rw [if_neg]
  rintro ⟨h0, -, -⟩
  exact h h0

theorem ep_nonnegX (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A)
    (s : S) {n : ℕ} (e : Episode M n) : 0 ≤ episodeProb M term μ s e := by
  unfold episodeProb
  split_ifs
  · exact prod_nonneg (fun k _ => mul_nonneg (μ.nonneg _ _) (M.p_nonneg _ _ _ _))
  · exact le_refl _

theorem decompX (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (n : ℕ) (X : Episode M (n + 1) → ℝ) :
    ∑ e, episodeProb M term μ s e * X e =
      if s ∈ term then 0 else
        ∑ a : A, ∑ s' : S, ∑ r : M.R, μ.prob s a * M.p s a s' r *
          ∑ e' : Episode M n, episodeProb M term μ s' e' * X (econsX s a r e') := by
  rw [sum_succX]
  simp_rw [epconsX]
  by_cases hs : s ∈ term
  · simp only [if_pos hs]
    apply sum_eq_zero; intro s0 _
    apply sum_eq_zero; intro a _
    apply sum_eq_zero; intro r _
    apply sum_eq_zero; intro e' _
    rw [if_neg (by rintro ⟨rfl, h⟩; exact h hs), zero_mul]
  · simp only [if_neg hs]
    rw [sum_eq_single s (fun s0 _ h0 => by
      apply sum_eq_zero; intro a _
      apply sum_eq_zero; intro r _
      apply sum_eq_zero; intro e' _
      rw [if_neg (by rintro ⟨h, -⟩; exact h0 h), zero_mul]) (by simp)]
    simp only [true_and, ite_true, hs, not_false_eq_true]
    refine sum_congr rfl (fun a _ => ?_)
    have h1 : ∀ (r : M.R) (e' : Episode M n),
        μ.prob s a * M.p s a (e'.1 0) r * episodeProb M term μ (e'.1 0) e' * X (econsX s a r e') =
        ∑ s' : S, μ.prob s a * M.p s a s' r * (episodeProb M term μ s' e' * X (econsX s a r e')) := by
      intro r e'
      rw [sum_eq_single (e'.1 0) (fun s' _ hs' => by
        rw [ep_ne_zeroX M term μ s' e' (Ne.symm hs')]; ring) (by simp)]
      ring
    simp_rw [h1, mul_sum]
    exact (sum_congr rfl (fun r _ => Finset.sum_comm)).trans Finset.sum_comm

theorem zeroX (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (X : Episode M 0 → ℝ) :
    ∑ e, episodeProb M term μ s e * X e =
      if s ∈ term then X (fun _ => s, Fin.elim0, Fin.elim0) else 0 := by
  rw [Fintype.sum_eq_single ((fun _ => s, Fin.elim0, Fin.elim0) : Episode M 0)]
  · unfold episodeProb Episode.states
    by_cases hs : s ∈ term <;> simp [hs]
  · intro e he
    rw [ep_ne_zeroX M term μ s e, zero_mul]
    intro h0
    apply he
    obtain ⟨f, g, h⟩ := e
    refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    funext i
    fin_cases i
    exact h0

theorem isr_consX (π b : SuttonBartoRL.FiniteMDP.Policy S A) {M : MDP S A} {n : ℕ} (s : S) (a : A)
    (r : M.R) (e' : Episode M n) (j : ℕ) :
    (econsX s a r e').isRatio π b (j + 1) = π.prob s a / b.prob s a * e'.isRatio π b j := by
  unfold Episode.isRatio econsX Episode.states Episode.actions
  rw [prod_filter, prod_filter, Fin.prod_univ_succ]
  simp only [Fin.val_zero, Nat.zero_lt_succ, ite_true, Fin.castSucc_zero, Fin.cons_zero,
    Fin.val_succ, Nat.add_lt_add_iff_right, ← Fin.succ_castSucc, Fin.cons_succ]

theorem isr_zeroX (π b : SuttonBartoRL.FiniteMDP.Policy S A) {M : MDP S A} {n : ℕ}
    (e : Episode M n) : e.isRatio π b 0 = 1 := by
  unfold Episode.isRatio
  simp

theorem rew_cons0X {M : MDP S A} {n : ℕ} (s : S) (a : A) (r : M.R) (e' : Episode M n) :
    (econsX s a r e').rewardAt 0 = (r : ℝ) := by
  unfold Episode.rewardAt Episode.rewards econsX
  rw [dif_pos (Nat.succ_pos n)]
  rfl

theorem rew_consX {M : MDP S A} {n : ℕ} (s : S) (a : A) (r : M.R) (e' : Episode M n) (j : ℕ) :
    (econsX s a r e').rewardAt (j + 1) = e'.rewardAt j := by
  unfold Episode.rewardAt Episode.rewards econsX
  by_cases h : j < n
  · rw [dif_pos (by omega), dif_pos h]
    have : (⟨j + 1, by omega⟩ : Fin (n + 1)) = Fin.succ ⟨j, h⟩ := rfl
    rw [this]; rfl
  · rw [dif_neg (by omega), dif_neg h]

theorem rew_ep0X {M : MDP S A} (e : Episode M 0) (j : ℕ) : e.rewardAt j = 0 := by
  unfold Episode.rewardAt
  rw [dif_neg (by omega)]

theorem swapX {M : MDP S A} (R : Finset ℕ) (w : A → S → M.R → ℝ) (c : ℕ → A → S → M.R → ℝ) :
    ∑ n ∈ R, ∑ a, ∑ s', ∑ r, w a s' r * c n a s' r =
      ∑ a, ∑ s', ∑ r, w a s' r * ∑ n ∈ R, c n a s' r := by
  simp only [mul_sum]
  exact Finset.sum_comm.trans (sum_congr rfl fun a _ => Finset.sum_comm.trans
    (sum_congr rfl fun s' _ => Finset.sum_comm))

theorem totX (M : MDP S A) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) :
    ∑ a : A, ∑ s' : S, ∑ r : M.R, μ.prob s a * M.p s a s' r = 1 := by
  have : ∀ a, ∑ s' : S, ∑ r : M.R, μ.prob s a * M.p s a s' r = μ.prob s a := by
    intro a
    simp_rw [← mul_sum]
    rw [show ∑ s' : S, ∑ r : M.R, M.p s a s' r = 1 by
      rw [← M.p_sum s a]
      exact sum_congr rfl (fun s' _ => Finset.sum_coe_sort M.R (fun r => M.p s a s' r)), mul_one]
  simp_rw [this]
  exact μ.sum_one s

theorem rangeX (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (N : ℕ) (X : (n : ℕ) → Episode M n → ℝ) :
    ∑ n ∈ range (N + 2), ∑ e : Episode M n, episodeProb M term μ s e * X n e =
      (if s ∈ term then X 0 (fun _ => s, Fin.elim0, Fin.elim0) else 0) +
      (if s ∈ term then 0 else
        ∑ a : A, ∑ s' : S, ∑ r : M.R, μ.prob s a * M.p s a s' r *
          ∑ n ∈ range (N + 1), ∑ e' : Episode M n,
            episodeProb M term μ s' e' * X (n + 1) (econsX s a r e')) := by
  rw [sum_range_succ', zeroX, add_comm]
  congr 1
  simp_rw [decompX]
  by_cases hs : s ∈ term
  · simp [hs]
  · simp only [hs, if_false]
    exact swapX (M := M) (range (N + 1)) (fun a s' r => μ.prob s a * M.p s a s' r)
      (fun n a s' r => ∑ e' : Episode M n, episodeProb M term μ s' e' * X (n + 1) (econsX s a r e'))

theorem subprobX (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) :
    ∀ N s, ∑ n ∈ range (N + 1), ∑ e : Episode M n, episodeProb M term μ s e ≤ 1 := by
  intro N
  induction N with
  | zero =>
    intro s
    have := zeroX M term μ s (fun _ => 1)
    simp only [mul_one] at this
    simp only [zero_add, range_one, sum_singleton, this]
    split_ifs <;> norm_num
  | succ N ih =>
    intro s
    have := rangeX M term μ s N (fun _ _ => 1)
    simp only [mul_one] at this
    rw [this]
    by_cases hs : s ∈ term
    · simp [hs]
    · simp only [hs, if_false, zero_add]
      calc _ ≤ ∑ a : A, ∑ s' : S, ∑ r : M.R, μ.prob s a * M.p s a s' r * 1 := by
            apply sum_le_sum; intro a _; apply sum_le_sum; intro s' _; apply sum_le_sum; intro r _
            exact mul_le_mul_of_nonneg_left (ih s') (mul_nonneg (μ.nonneg _ _) (M.p_nonneg _ _ _ _))
        _ = 1 := by simp only [mul_one]; exact totX M μ s

def TermX (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (N : ℕ) : Prop :=
  ∑ n ∈ range (N + 1), ∑ e : Episode M n, episodeProb M term μ s e = 1

theorem propX (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (N : ℕ) (hT : TermX M term μ s (N + 1)) (hs : s ∉ term) (a : A) (s' : S) (r : M.R)
    (hw : 0 < μ.prob s a * M.p s a s' r) : TermX M term μ s' N := by
  unfold TermX at hT ⊢
  have h := rangeX M term μ s N (fun _ _ => 1)
  simp only [mul_one, hs, if_false, zero_add] at h
  rw [h] at hT
  by_contra hne
  have hlt : ∑ n ∈ range (N + 1), ∑ e : Episode M n, episodeProb M term μ s' e < 1 :=
    lt_of_le_of_ne (subprobX M term μ N s') hne
  have hle : ∀ a s' (r : M.R), μ.prob s a * M.p s a s' r *
      (∑ n ∈ range (N + 1), ∑ e : Episode M n, episodeProb M term μ s' e) ≤
      μ.prob s a * M.p s a s' r * 1 := fun a s' r =>
    mul_le_mul_of_nonneg_left (subprobX M term μ N s') (mul_nonneg (μ.nonneg _ _) (M.p_nonneg _ _ _ _))
  have hstrict : ∑ a : A, ∑ s' : S, ∑ r : M.R, μ.prob s a * M.p s a s' r *
      (∑ n ∈ range (N + 1), ∑ e : Episode M n, episodeProb M term μ s' e) <
      ∑ a : A, ∑ s' : S, ∑ r : M.R, μ.prob s a * M.p s a s' r * 1 := by
    apply Finset.sum_lt_sum (fun a _ => sum_le_sum fun s' _ => sum_le_sum fun r _ => hle a s' r)
    refine ⟨a, mem_univ _, ?_⟩
    apply Finset.sum_lt_sum (fun s' _ => sum_le_sum fun r _ => hle a s' r)
    refine ⟨s', mem_univ _, ?_⟩
    apply Finset.sum_lt_sum (fun r _ => hle a s' r)
    exact ⟨r, mem_univ _, mul_lt_mul_of_pos_left hlt hw⟩
  simp only [mul_one, totX] at hstrict
  linarith

theorem term0X (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (hT : TermX M term μ s 0) : s ∈ term := by
  unfold TermX at hT
  have := zeroX M term μ s (fun _ => 1)
  simp only [mul_one] at this
  simp only [zero_add, range_one, sum_singleton, this] at hT
  by_contra h
  rw [if_neg h] at hT
  norm_num at hT

theorem weightX (M : MDP S A) (π b : SuttonBartoRL.FiniteMDP.Policy S A) (hcov : Coverage π b)
    (s : S) (a : A) (s' : S) (r : M.R) (c : ℝ)
    (hc : 0 < b.prob s a * M.p s a s' r → c = 1) :
    b.prob s a * M.p s a s' r * (π.prob s a / b.prob s a * c) = π.prob s a * M.p s a s' r := by
  by_cases hw : 0 < b.prob s a * M.p s a s' r
  · rw [hc hw, mul_one]
    have hb : b.prob s a ≠ 0 := by
      intro h; rw [h, zero_mul] at hw; exact lt_irrefl _ hw
    field_simp
  · have hw0 : b.prob s a * M.p s a s' r = 0 :=
      le_antisymm (not_lt.mp hw) (mul_nonneg (b.nonneg _ _) (M.p_nonneg _ _ _ _))
    rcases mul_eq_zero.mp hw0 with h | h
    · have hπ : π.prob s a = 0 := by
        by_contra hne
        have := hcov s a (lt_of_le_of_ne (π.nonneg _ _) (Ne.symm hne))
        rw [h] at this; exact lt_irrefl _ this
      rw [hπ, h]; ring
    · rw [h]; ring

theorem fullX (M : MDP S A) (term : Finset S) (π b : SuttonBartoRL.FiniteMDP.Policy S A)
    (hcov : Coverage π b) :
    ∀ N s, TermX M term b s N →
      ∑ n ∈ range (N + 1), ∑ e : Episode M n, episodeProb M term b s e * e.isRatio π b n = 1 := by
  intro N
  induction N with
  | zero =>
    intro s hT
    simp only [zero_add, range_one, sum_singleton, isr_zeroX, mul_one]
    unfold TermX at hT
    simpa using hT
  | succ N ih =>
    intro s hT
    rw [rangeX M term b s N (fun n e => e.isRatio π b n)]
    by_cases hs : s ∈ term
    · simp [hs, isr_zeroX]
    · simp only [hs, if_false, zero_add]
      simp_rw [isr_consX, mul_left_comm _ (π.prob s _ / b.prob s _), ← mul_sum]
      have : ∀ a s' (r : M.R), b.prob s a * M.p s a s' r * (π.prob s a / b.prob s a *
          ∑ n ∈ range (N + 1), ∑ e' : Episode M n, episodeProb M term b s' e' * e'.isRatio π b n) =
          π.prob s a * M.p s a s' r := fun a s' r =>
        weightX M π b hcov s a s' r _ (fun hw => ih s' (propX M term b s N hT hs a s' r hw))
      simp_rw [this]
      exact totX M π s

theorem mainX (M : MDP S A) (term : Finset S) (π b : SuttonBartoRL.FiniteMDP.Policy S A)
    (hcov : Coverage π b) :
    ∀ j N s, TermX M term b s N →
      ∑ n ∈ range (N + 1), ∑ e : Episode M n,
          episodeProb M term b s e * (e.isRatio π b n * e.rewardAt j) =
        ∑ n ∈ range (N + 1), ∑ e : Episode M n,
          episodeProb M term b s e * (e.isRatio π b (j + 1) * e.rewardAt j) := by
  intro j
  induction j with
  | zero =>
    intro N s hT
    rcases N with _ | N
    · simp [rew_ep0X]
    · rw [rangeX M term b s N (fun n e => e.isRatio π b n * e.rewardAt 0),
        rangeX M term b s N (fun n e => e.isRatio π b 1 * e.rewardAt 0)]
      simp only [rew_ep0X, mul_zero, ite_self, zero_add]
      by_cases hs : s ∈ term
      · simp [hs]
      · simp only [hs, if_false]
        refine sum_congr rfl fun a _ => sum_congr rfl fun s' _ => sum_congr rfl fun r _ => ?_
        by_cases hw : 0 < b.prob s a * M.p s a s' r
        · have hT' := propX M term b s N hT hs a s' r hw
          have hF := fullX M term π b hcov N s' hT'
          unfold TermX at hT'
          congr 1
          simp_rw [isr_consX, rew_cons0X, isr_zeroX]
          have e1 : ∀ n (e' : Episode M n), episodeProb M term b s' e' *
              (π.prob s a / b.prob s a * e'.isRatio π b n * (r : ℝ)) =
              (π.prob s a / b.prob s a * r) * (episodeProb M term b s' e' * e'.isRatio π b n) :=
            fun n e' => by ring
          have e2 : ∀ n (e' : Episode M n), episodeProb M term b s' e' *
              (π.prob s a / b.prob s a * 1 * (r : ℝ)) =
              (π.prob s a / b.prob s a * r) * episodeProb M term b s' e' := fun n e' => by ring
          simp_rw [e1, e2, ← mul_sum, hF, hT']
        · have hw0 : b.prob s a * M.p s a s' r = 0 :=
            le_antisymm (not_lt.mp hw) (mul_nonneg (b.nonneg _ _) (M.p_nonneg _ _ _ _))
          rw [hw0, zero_mul, zero_mul]
  | succ j ih =>
    intro N s hT
    rcases N with _ | N
    · simp [rew_ep0X]
    · rw [rangeX M term b s N (fun n e => e.isRatio π b n * e.rewardAt (j + 1)),
        rangeX M term b s N (fun n e => e.isRatio π b (j + 2) * e.rewardAt (j + 1))]
      simp only [rew_ep0X, mul_zero, ite_self, zero_add]
      by_cases hs : s ∈ term
      · simp [hs]
      · simp only [hs, if_false]
        refine sum_congr rfl fun a _ => sum_congr rfl fun s' _ => sum_congr rfl fun r _ => ?_
        by_cases hw : 0 < b.prob s a * M.p s a s' r
        · have hT' := propX M term b s N hT hs a s' r hw
          have hI := ih N s' hT'
          congr 1
          simp_rw [isr_consX, rew_consX]
          have e1 : ∀ m n (e' : Episode M n), episodeProb M term b s' e' *
              (π.prob s a / b.prob s a * e'.isRatio π b m * e'.rewardAt j) =
              (π.prob s a / b.prob s a) * (episodeProb M term b s' e' *
                (e'.isRatio π b m * e'.rewardAt j)) := fun m n e' => by ring
          simp_rw [e1, ← mul_sum, hI]
        · have hw0 : b.prob s a * M.p s a s' r = 0 :=
            le_antisymm (not_lt.mp hw) (mul_nonneg (b.nonneg _ _) (M.p_nonneg _ _ _ _))
          rw [hw0, zero_mul, zero_mul]

theorem vanishX (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (H : ℕ) (hT : TermX M term μ s H) (n : ℕ) (hn : H < n) (e : Episode M n) :
    episodeProb M term μ s e = 0 := by
  have hsub := subprobX M term μ n s
  have hnn : ∀ m, 0 ≤ ∑ e : Episode M m, episodeProb M term μ s e :=
    fun m => sum_nonneg fun e _ => ep_nonnegX M term μ s e
  have hnot : n ∉ range (H + 1) := by simp; omega
  have hle : ∑ m ∈ insert n (range (H + 1)), ∑ e : Episode M m, episodeProb M term μ s e ≤
      ∑ m ∈ range (n + 1), ∑ e : Episode M m, episodeProb M term μ s e := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      simp only [mem_insert, mem_range] at hm ⊢
      omega
    · intro m _ _; exact hnn m
  rw [sum_insert hnot] at hle
  unfold TermX at hT
  rw [hT] at hle
  have h0 : ∑ e : Episode M n, episodeProb M term μ s e = 0 :=
    le_antisymm (by linarith) (hnn n)
  exact (sum_eq_zero_iff_of_nonneg (fun e _ => ep_nonnegX M term μ s e)).mp h0 e (mem_univ _)

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (term : Finset S) (π b : SuttonBartoRL.FiniteMDP.Policy S A) (hcov : Coverage π b) (s : S) (H : ℕ)
    (hH : ∑ n ∈ Finset.range (H + 1), ∑ e : Episode M n, episodeProb M term b s e = 1)
    (k : ℕ) (hk : 1 ≤ k) :
    expectation M term b s (fun n e => e.isRatio π b n * e.rewardAt (k - 1)) =
      expectation M term b s (fun _ e => e.isRatio π b k * e.rewardAt (k - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hT : TermX M term b s H := hH
  unfold expectation
  have hz : ∀ (X : (n : ℕ) → Episode M n → ℝ) n, n ∉ range (H + 1) →
      ∑ e : Episode M n, episodeProb M term b s e * X n e = 0 := by
    intro X n hn
    simp only [mem_range, not_lt] at hn
    exact sum_eq_zero fun e _ => by rw [vanishX M term b s H hT n (by omega) e, zero_mul]
  rw [tsum_eq_sum (hz (fun n e => e.isRatio π b n * e.rewardAt j)),
    tsum_eq_sum (hz (fun _ e => e.isRatio π b (j + 1) * e.rewardAt j))]
  exact mainX M term π b hcov j H s hT
