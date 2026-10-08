-- Prove2me | solution 1 for SuttonBartoRL.ImportanceSampling.importance_sampling_unbiased
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:05:11.348869+00:00
-- url     : https://prove2.me/submissions/5e12304e-d4af-401e-a0b0-53c2b0c26eb5

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_Episodes

set_option autoImplicit false

namespace A32Aux

open SuttonBartoRL.ImportanceSampling

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

def cons {M : MDP S A} {n : ℕ} (s0 : S) (a : A) (r : M.R) (e : Episode M n) :
    Episode M (n + 1) :=
  (Fin.cons s0 e.1, Fin.cons a e.2.1, Fin.cons r e.2.2)

def consEquiv (M : MDP S A) (n : ℕ) : S × A × M.R × Episode M n ≃ Episode M (n + 1) where
  toFun x := cons x.1 x.2.1 x.2.2.1 x.2.2.2
  invFun e := (e.1 0, e.2.1 0, e.2.2 0, (Fin.tail e.1, Fin.tail e.2.1, Fin.tail e.2.2))
  left_inv x := by
    obtain ⟨s0, a, r, st, ac, rw⟩ := x
    simp [cons]
  right_inv e := by
    obtain ⟨st, ac, rw⟩ := e
    simp [cons, Fin.cons_self_tail]

lemma sum_succ (M : MDP S A) (n : ℕ) (F : Episode M (n + 1) → ℝ) :
    ∑ e, F e = ∑ s0 : S, ∑ a : A, ∑ r : M.R, ∑ e' : Episode M n, F (cons s0 a r e') := by
  rw [← (consEquiv M n).sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

lemma prob_nonneg (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A)
    (s : S) {n : ℕ} (e : Episode M n) : 0 ≤ episodeProb M term μ s e := by
  unfold episodeProb
  split_ifs
  · exact Finset.prod_nonneg fun k _ => mul_nonneg (μ.nonneg _ _) (M.p_nonneg _ _ _ _)
  · exact le_refl 0

lemma prob_ne (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A)
    (s : S) {n : ℕ} (e : Episode M n) (h : e.1 0 ≠ s) : episodeProb M term μ s e = 0 := by
  unfold episodeProb
  rw [if_neg]
  rintro ⟨h1, -⟩
  exact h h1

lemma prob_cons (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A)
    (s : S) {n : ℕ} (s0 : S) (a : A) (r : M.R) (e : Episode M n) :
    episodeProb M term μ s (cons s0 a r e) =
      if s0 = s ∧ s0 ∉ term then
        μ.prob s0 a * M.p s0 a (e.1 0) r * episodeProb M term μ (e.1 0) e
      else 0 := by
  obtain ⟨st, ac, rw⟩ := e
  unfold episodeProb
  simp only [cons, Episode.states, Episode.actions, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.castSucc_zero, Fin.cons_succ, Fin.forall_fin_succ, ← Fin.succ_castSucc, ← Fin.succ_last]
  by_cases h : s0 = s ∧ s0 ∉ term
  · by_cases h2 : (∀ k : Fin n, st k.castSucc ∉ term) ∧ st (Fin.last n) ∈ term
    · rw [if_pos ⟨h.1, ⟨h.2, h2.1⟩, h2.2⟩, if_pos h, if_pos ⟨trivial, h2⟩]
    · rw [if_neg (fun h' => h2 ⟨h'.2.1.2, h'.2.2⟩), if_pos h, if_neg (fun h' => h2 h'.2), mul_zero]
  · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1.1⟩), if_neg h]

/-- level sum -/
noncomputable def L (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (X : (n : ℕ) → Episode M n → ℝ) (n : ℕ) : ℝ :=
  ∑ e : Episode M n, episodeProb M term μ s e * X n e

lemma collapse (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) {n : ℕ}
    (g : S → Episode M n → ℝ) :
    ∑ e : Episode M n, episodeProb M term μ (e.1 0) e * g (e.1 0) e =
      ∑ s1 : S, ∑ e : Episode M n, episodeProb M term μ s1 e * g s1 e := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_eq_single (e.1 0)]
  · intro s1 _ hne
    rw [prob_ne M term μ s1 e (Ne.symm hne), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma L_succ (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (X : (n : ℕ) → Episode M n → ℝ) (n : ℕ) :
    L M term μ s X (n + 1) =
      if s ∉ term then
        ∑ a : A, ∑ s1 : S, ∑ r : M.R, μ.prob s a * M.p s a s1 r *
          ∑ e : Episode M n, episodeProb M term μ s1 e * X (n + 1) (cons s a r e)
      else 0 := by
  unfold L
  rw [sum_succ]
  simp_rw [prob_cons]
  rw [Fintype.sum_eq_single s (fun s0 hne => by simp [hne])]
  · by_cases hs : s ∈ term
    · simp [hs]
    · simp only [hs, not_false_eq_true, and_self, if_true]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm (s := (Finset.univ : Finset S)) (t := (Finset.univ : Finset M.R))]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [show (∑ e : Episode M n, μ.prob s a * M.p s a (e.1 0) ↑r *
            episodeProb M term μ (e.1 0) e * X (n + 1) (cons s a r e)) =
          ∑ e : Episode M n, episodeProb M term μ (e.1 0) e *
            (fun s1 e => μ.prob s a * M.p s a s1 ↑r * X (n + 1) (cons s a r e)) (e.1 0) e from
          Finset.sum_congr rfl fun _ _ => by ring]
      refine Eq.trans (collapse M term μ (n := n)
        (fun s1 e => μ.prob s a * M.p s a s1 ↑r * X (n + 1) (cons s a r e))) ?_
      refine Finset.sum_congr rfl fun s1 _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring

lemma ret_cons {M : MDP S A} {n : ℕ} (γ : ℝ) (s0 : S) (a : A) (r : M.R) (e : Episode M n) :
    (cons s0 a r e).ret γ = (r : ℝ) + γ * e.ret γ := by
  unfold Episode.ret Episode.rewards
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [cons, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma isRatio_cons {M : MDP S A} {n : ℕ} (π b : SuttonBartoRL.FiniteMDP.Policy S A)
    (s0 : S) (a : A) (r : M.R) (e : Episode M n) (j : ℕ) :
    (cons s0 a r e).isRatio π b (j + 1) = π.prob s0 a / b.prob s0 a * e.isRatio π b j := by
  unfold Episode.isRatio
  rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
  simp [cons, Episode.states, Episode.actions]

lemma isRatio_zero {M : MDP S A} {n : ℕ} (π b : SuttonBartoRL.FiniteMDP.Policy S A)
    (e : Episode M n) : e.isRatio π b 0 = 1 := by
  simp [Episode.isRatio]

lemma pd_cons {M : MDP S A} {n : ℕ} (π b : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ)
    (s0 : S) (a : A) (r : M.R) (e : Episode M n) :
    (cons s0 a r e).perDecisionReturn π b γ =
      π.prob s0 a / b.prob s0 a * ((r : ℝ) + γ * e.perDecisionReturn π b γ) := by
  unfold Episode.perDecisionReturn
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.val_zero, Fin.val_succ, isRatio_cons, zero_add, isRatio_zero, mul_one]
  simp only [Episode.rewards, cons, Fin.cons_zero, Fin.cons_succ]
  rw [mul_add]
  congr 1
  · ring
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

abbrev Xone (M : MDP S A) : (n : ℕ) → Episode M n → ℝ := fun _ _ => 1
abbrev Xret (M : MDP S A) (γ : ℝ) : (n : ℕ) → Episode M n → ℝ := fun _ e => e.ret γ
noncomputable abbrev Xpd (M : MDP S A) (π b : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) :
    (n : ℕ) → Episode M n → ℝ := fun _ e => e.perDecisionReturn π b γ

noncomputable def E (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (X : (n : ℕ) → Episode M n → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), L M term μ s X n

lemma L_zero_nt (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (hs : s ∉ term) (X : (n : ℕ) → Episode M n → ℝ) : L M term μ s X 0 = 0 := by
  unfold L
  apply Finset.sum_eq_zero
  intro e _
  unfold episodeProb
  rw [if_neg, zero_mul]
  rintro ⟨h1, -, h2⟩
  have hl : Fin.last 0 = (0 : Fin 1) := rfl
  rw [hl, h1] at h2
  exact hs h2

lemma L_zero_ret (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (γ : ℝ) : L M term μ s (Xret M γ) 0 = 0 := by
  unfold L
  simp [Episode.ret]

lemma L_zero_pd (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (π b : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) : L M term μ s (Xpd M π b γ) 0 = 0 := by
  unfold L
  simp [Episode.perDecisionReturn]

lemma L_zero_indep (M : MDP S A) (term : Finset S) (μ ν : SuttonBartoRL.FiniteMDP.Policy S A)
    (s : S) : L M term μ s (Xone M) 0 = L M term ν s (Xone M) 0 := by
  unfold L
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold episodeProb
  simp

lemma L_zero_le (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) :
    L M term μ s (Xone M) 0 ≤ 1 := by
  unfold L
  let e0 : Episode M 0 := ((fun _ => s), (fun i => Fin.elim0 i), (fun i => Fin.elim0 i))
  calc ∑ e : Episode M 0, episodeProb M term μ s e * (Xone M) 0 e
      ≤ ∑ e : Episode M 0, (if e = e0 then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun e _ => ?_
        obtain ⟨st, ac, rw⟩ := e
        simp only [Xone, mul_one]
        have key : st 0 = s → ((st, ac, rw) : Episode M 0) = e0 := by
          intro h0
          simp only [e0, Prod.mk.injEq]
          refine ⟨funext fun i => ?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
          rw [Fin.fin_one_eq_zero i]
          exact h0
        by_cases he : ((st, ac, rw) : Episode M 0) = e0
        · rw [if_pos he]
          unfold episodeProb
          split_ifs
          · simp
          · norm_num
        · rw [if_neg he]
          unfold episodeProb
          split_ifs with h1
          · exact absurd (key h1.1) he
          · exact le_refl 0
    _ = 1 := by simp

lemma E_term (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (hs : s ∈ term) (X : (n : ℕ) → Episode M n → ℝ) (N : ℕ) : E M term μ s X N = L M term μ s X 0 := by
  unfold E
  rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun n _ => by rw [L_succ, if_neg (not_not.2 hs)]),
    zero_add]

lemma swap3 {α β δ : Type} [Fintype α] [Fintype β] [Fintype δ] (N : ℕ) (f : ℕ → α → β → δ → ℝ) :
    ∑ n ∈ Finset.range N, ∑ a, ∑ b, ∑ c, f n a b c = ∑ a, ∑ b, ∑ c, ∑ n ∈ Finset.range N, f n a b c := by
  rw [Finset.sum_comm (s := Finset.range N) (t := (Finset.univ : Finset α))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (s := Finset.range N) (t := (Finset.univ : Finset β))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm (s := Finset.range N) (t := (Finset.univ : Finset δ))]

lemma T_succ (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (hs : s ∉ term) (N : ℕ) :
    E M term μ s (Xone M) (N + 1) =
      ∑ a : A, ∑ s1 : S, ∑ r : M.R, μ.prob s a * M.p s a s1 r * E M term μ s1 (Xone M) N := by
  unfold E
  rw [Finset.sum_range_succ', L_zero_nt M term μ s hs, add_zero]
  simp only [L_succ, if_pos hs]
  rw [swap3]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s1 _ =>
    Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  rfl

lemma Eret_succ (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (hs : s ∉ term) (γ : ℝ) (N : ℕ) :
    E M term μ s (Xret M γ) (N + 1) =
      ∑ a : A, ∑ s1 : S, ∑ r : M.R, μ.prob s a * M.p s a s1 r *
        ((r : ℝ) * E M term μ s1 (Xone M) N + γ * E M term μ s1 (Xret M γ) N) := by
  unfold E
  rw [Finset.sum_range_succ', L_zero_nt M term μ s hs, add_zero]
  simp only [L_succ, if_pos hs]
  rw [swap3]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s1 _ =>
    Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold L
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Xret, Xone, ret_cons]
  ring

lemma Epd_succ (M : MDP S A) (term : Finset S) (π b : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (hs : s ∉ term) (γ : ℝ) (N : ℕ) :
    E M term b s (Xpd M π b γ) (N + 1) =
      ∑ a : A, ∑ s1 : S, ∑ r : M.R, b.prob s a * M.p s a s1 r * (π.prob s a / b.prob s a) *
        ((r : ℝ) * E M term b s1 (Xone M) N + γ * E M term b s1 (Xpd M π b γ) N) := by
  unfold E
  rw [Finset.sum_range_succ', L_zero_nt M term b s hs, add_zero]
  simp only [L_succ, if_pos hs]
  rw [swap3]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s1 _ =>
    Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.mul_sum, mul_assoc (b.prob s a * M.p s a s1 r)]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold L
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Xpd, Xone, pd_cons]
  ring

lemma sum_one (M : MDP S A) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) :
    ∑ a : A, ∑ s1 : S, ∑ r : M.R, μ.prob s a * M.p s a s1 r = 1 := by
  have h : ∀ a, ∑ s1 : S, ∑ r : M.R, M.p s a s1 r = 1 := fun a => by
    rw [← M.p_sum s a]
    exact Finset.sum_congr rfl fun s1 _ => Finset.sum_coe_sort M.R (fun r => M.p s a s1 r)
  simp_rw [← Finset.mul_sum, h, mul_one]
  exact μ.sum_one s

lemma T_le (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) :
    ∀ N s, E M term μ s (Xone M) N ≤ 1 := by
  intro N
  induction N with
  | zero => intro s; unfold E; rw [Finset.sum_range_one]; exact L_zero_le M term μ s
  | succ N ih =>
    intro s
    by_cases hs : s ∈ term
    · rw [E_term M term μ s hs]; exact L_zero_le M term μ s
    · rw [T_succ M term μ s hs]
      calc _ ≤ ∑ a : A, ∑ s1 : S, ∑ r : M.R, μ.prob s a * M.p s a s1 r * 1 := by
            refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun s1 _ =>
              Finset.sum_le_sum fun r _ => ?_
            exact mul_le_mul_of_nonneg_left (ih s1) (mul_nonneg (μ.nonneg _ _) (M.p_nonneg _ _ _ _))
        _ = 1 := by simp only [mul_one]; exact sum_one M μ s

lemma L_one_nonneg (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (n : ℕ) : 0 ≤ L M term μ s (Xone M) n :=
  Finset.sum_nonneg fun e _ => by simp only [Xone, mul_one]; exact prob_nonneg M term μ s e

lemma trunc (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) (H : ℕ)
    (hT : E M term μ s (Xone M) H = 1) (n : ℕ) (hn : H < n) (X : (n : ℕ) → Episode M n → ℝ) :
    L M term μ s X n = 0 := by
  have h1 := T_le M term μ n s
  have h2 : E M term μ s (Xone M) H ≤ ∑ k ∈ Finset.range n, L M term μ s (Xone M) k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (show H + 1 ≤ n by omega))
      (fun k _ _ => L_one_nonneg M term μ s k)
  have h3 : L M term μ s (Xone M) n = 0 := by
    unfold E at h1
    rw [Finset.sum_range_succ] at h1
    exact le_antisymm (by linarith) (L_one_nonneg M term μ s n)
  unfold L at h3 ⊢
  simp only [Xone, mul_one] at h3
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun e _ => prob_nonneg M term μ s e)] at h3
  exact Finset.sum_eq_zero fun e he => by rw [h3 e he, zero_mul]

lemma cov_zero {π b : SuttonBartoRL.FiniteMDP.Policy S A} (hcov : Coverage π b) (s : S) (a : A)
    (hb : b.prob s a = 0) : π.prob s a = 0 :=
  le_antisymm (not_lt.1 fun h => (hcov s a h).ne' hb) (π.nonneg s a)

lemma main (M : MDP S A) (term : Finset S) (π b : SuttonBartoRL.FiniteMDP.Policy S A)
    (hcov : Coverage π b) (γ : ℝ) :
    ∀ N s, E M term b s (Xone M) N = 1 →
      E M term b s (Xpd M π b γ) N = E M term π s (Xret M γ) N ∧ E M term π s (Xone M) N = 1 := by
  intro N
  induction N with
  | zero =>
    intro s hT
    unfold E at hT ⊢
    simp only [zero_add, Finset.sum_range_one] at hT ⊢
    refine ⟨by rw [L_zero_pd, L_zero_ret], by rw [L_zero_indep M term π b]; exact hT⟩
  | succ N ih =>
    intro s hT
    by_cases hs : s ∈ term
    · rw [E_term M term b s hs] at hT
      rw [E_term M term b s hs, E_term M term π s hs, E_term M term π s hs, L_zero_pd, L_zero_ret,
        L_zero_indep M term π b]
      exact ⟨rfl, hT⟩
    · rw [T_succ M term b s hs] at hT
      -- every b-reachable successor has full termination mass
      have key : ∀ a s1 (r : M.R), b.prob s a * M.p s a s1 r ≠ 0 → E M term b s1 (Xone M) N = 1 := by
        have hz : ∑ a : A, ∑ s1 : S, ∑ r : M.R,
            b.prob s a * M.p s a s1 r * (1 - E M term b s1 (Xone M) N) = 0 := by
          simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hT, sum_one M b s, sub_self]
        have hnn : ∀ a s1 (r : M.R), 0 ≤ b.prob s a * M.p s a s1 r * (1 - E M term b s1 (Xone M) N) :=
          fun a s1 r => mul_nonneg (mul_nonneg (b.nonneg _ _) (M.p_nonneg _ _ _ _))
            (sub_nonneg.2 (T_le M term b N s1))
        intro a s1 r hne
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun s1 _ =>
          Finset.sum_nonneg fun r _ => hnn a s1 r)] at hz
        have hz2 := hz a (Finset.mem_univ _)
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun s1 _ =>
          Finset.sum_nonneg fun r _ => hnn a s1 r)] at hz2
        have hz3 := hz2 s1 (Finset.mem_univ _)
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun r _ => hnn a s1 r)] at hz3
        have hz4 := hz3 r (Finset.mem_univ _)
        rcases mul_eq_zero.1 hz4 with h | h
        · exact absurd h hne
        · linarith
      -- π-positive transitions are b-positive
      have pos : ∀ a s1 (r : M.R), π.prob s a * M.p s a s1 r ≠ 0 → b.prob s a * M.p s a s1 r ≠ 0 := by
        intro a s1 r h
        have hπ : π.prob s a ≠ 0 := left_ne_zero_of_mul h
        have hp : M.p s a s1 r ≠ 0 := right_ne_zero_of_mul h
        exact mul_ne_zero (fun hb => hπ (cov_zero hcov s a hb)) hp
      refine ⟨?_, ?_⟩
      · rw [Epd_succ M term π b s hs, Eret_succ M term π s hs]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s1 _ =>
          Finset.sum_congr rfl fun r _ => ?_
        by_cases hw : b.prob s a * M.p s a s1 r = 0
        · have hw' : π.prob s a * M.p s a s1 r = 0 := by
            by_contra hc; exact pos a s1 r hc hw
          rw [hw, hw']; ring
        · have hT1 := key a s1 r hw
          obtain ⟨hE, hTπ⟩ := ih s1 hT1
          have hb : b.prob s a ≠ 0 := left_ne_zero_of_mul hw
          rw [hT1, hE, hTπ]
          field_simp
      · rw [T_succ M term π s hs]
        rw [← sum_one M π s]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s1 _ =>
          Finset.sum_congr rfl fun r _ => ?_
        by_cases hw : π.prob s a * M.p s a s1 r = 0
        · rw [hw, zero_mul]
        · rw [(ih s1 (key a s1 r (pos a s1 r hw))).2, mul_one]

lemma prob_change (M : MDP S A) (term : Finset S) (π b : SuttonBartoRL.FiniteMDP.Policy S A)
    (hcov : Coverage π b) (s : S) {n : ℕ} (e : Episode M n) :
    episodeProb M term b s e * e.isRatio π b n = episodeProb M term π s e := by
  unfold episodeProb Episode.isRatio
  rw [Finset.filter_true_of_mem (fun k _ => k.isLt)]
  split_ifs
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hb : b.prob (e.states k.castSucc) (e.actions k) = 0
    · rw [hb, cov_zero hcov _ _ hb]; ring
    · field_simp
  · rw [zero_mul]

end A32Aux

open SuttonBartoRL.ImportanceSampling in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (term : Finset S) (π b : SuttonBartoRL.FiniteMDP.Policy S A) (hcov : Coverage π b)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (s : S) (H : ℕ)
    (hH : ∑ n ∈ Finset.range (H + 1), ∑ e : Episode M n, episodeProb M term b s e = 1) :
    expectation M term b s (fun n e => e.isRatio π b n * e.ret γ) = value M term π γ s ∧
    expectation M term b s (fun _ e => e.perDecisionReturn π b γ) = value M term π γ s := by
  refine ⟨?_, ?_⟩
  · unfold value expectation
    congr 1
    funext n
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← mul_assoc, A32Aux.prob_change M term π b hcov s e]
  · have hTb : A32Aux.E M term b s (A32Aux.Xone M) H = 1 := by
      unfold A32Aux.E A32Aux.L
      simp only [A32Aux.Xone, mul_one]
      exact hH
    obtain ⟨hE, hTπ⟩ := A32Aux.main M term π b hcov γ H s hTb
    unfold value expectation
    show ∑' n, A32Aux.L M term b s (A32Aux.Xpd M π b γ) n = ∑' n, A32Aux.L M term π s (A32Aux.Xret M γ) n
    rw [tsum_eq_sum (s := Finset.range (H + 1)) (fun n hn =>
          A32Aux.trunc M term b s H hTb n (by simpa using hn) _),
        tsum_eq_sum (s := Finset.range (H + 1)) (fun n hn =>
          A32Aux.trunc M term π s H hTπ n (by simpa using hn) _)]
    exact hE
