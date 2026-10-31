-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.one_shot_deviation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:33:26.887031+00:00
-- url     : https://prove2.me/submissions/4b76dbad-026b-47c6-ac5e-5a9561e2d617

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

set_option linter.unusedSectionVars false

namespace TDFAux

open TimeDepFolk.Asymptotic Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

theorem histProb_nonneg (σ : Profile A) {T : ℕ} (h : History A T) : 0 ≤ histProb σ h := by
  unfold histProb
  exact Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun i _ => ((σ i).act_mem _ _).1 _

theorem take_snoc_castSucc {T : ℕ} (h : History A T) (a : ∀ i, A i) (r : Fin T) :
    History.take (Fin.snoc h a : History A (T + 1)) r.castSucc (Nat.le_of_lt r.castSucc.isLt) =
      h.take r (Nat.le_of_lt r.isLt) := by
  funext q
  simp only [History.take]
  have : (Fin.castLE (Nat.le_of_lt r.castSucc.isLt) q : Fin (T + 1)) =
      (Fin.castLE (Nat.le_of_lt r.isLt) q).castSucc := by ext; simp
  rw [this, Fin.snoc_castSucc]

theorem take_snoc_last {T : ℕ} (h : History A T) (a : ∀ i, A i) :
    History.take (Fin.snoc h a : History A (T + 1)) (Fin.last T) (Nat.le_of_lt (Fin.last T).isLt) = h := by
  funext q
  simp only [History.take]
  have : (Fin.castLE (Nat.le_of_lt (Fin.last T).isLt) q : Fin (T + 1)) = q.castSucc := by
    ext; simp
  rw [this, Fin.snoc_castSucc]

theorem histProb_snoc (σ : Profile A) {T : ℕ} (h : History A T) (a : ∀ i, A i) :
    histProb σ (Fin.snoc h a : History A (T + 1)) =
      histProb σ h * ∏ j, (σ j).act T h (a j) := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun r _ => ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 := take_snoc_castSucc h a r
    simp only [Fin.val_castSucc] at h1 ⊢
    rw [Fin.snoc_castSucc]
    exact congrArg (fun x => (σ i).act r x (h r i)) h1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have h1 := take_snoc_last h a
    simp only [Fin.val_last] at h1 ⊢
    rw [Fin.snoc_last]
    exact congrArg (fun x => (σ i).act T x (a i)) h1

theorem sum_snoc {T : ℕ} {M : Type*} [AddCommMonoid M] (f : History A (T + 1) → M) :
    ∑ h : History A (T + 1), f h = ∑ h : History A T, ∑ a : (∀ i, A i), f (Fin.snoc h a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (T + 1) => ∀ i, A i)).sum_comp, Fintype.sum_prod_type_right]
  rfl

theorem sum_prob_profile (μ : ∀ j, A j → ℝ) (hμ : ∀ j, AGT.IsLottery (μ j)) :
    ∑ a : (∀ j, A j), ∏ j, μ j (a j) = 1 := by
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun j _ => (hμ j).2

theorem sum_histProb (σ : Profile A) : ∀ T : ℕ, ∑ h : History A T, histProb σ h = 1
  | 0 => by simp [histProb]
  | T + 1 => by
    rw [sum_snoc]
    simp_rw [histProb_snoc, ← Finset.mul_sum]
    rw [← sum_histProb σ T]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [sum_prob_profile _ (fun j => (σ j).act_mem T h), mul_one]

theorem stageExp_eq (g : I → (∀ i, A i) → ℝ) (σ : Profile A) (i : I) (s : ℕ) :
    stageExp g σ i s = ∑ h : History A s,
      histProb σ h * AGT.expectedPayoff g (fun j => (σ j).act s h) i := by
  unfold stageExp
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [histProb_snoc, Fin.snoc_last, AGT.expectedPayoff, AGT.profileProb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring


theorem exists_bound (g : I → (∀ i, A i) → ℝ) : ∃ M, 0 < M ∧ ∀ i a, |g i a| ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range (fun p : I × (∀ i, A i) => |g p.1 p.2|)).bddAbove
  refine ⟨max M 1, by positivity, fun i a => ?_⟩
  exact (hM ⟨(i, a), rfl⟩).trans (le_max_left _ _)

theorem abs_stageExp_le (g : I → (∀ i, A i) → ℝ) (σ : Profile A) (i : I) (s : ℕ) (M : ℝ)
    (hM : ∀ i a, |g i a| ≤ M) : |stageExp g σ i s| ≤ M := by
  unfold stageExp
  calc |∑ h : History A (s + 1), histProb σ h * g i (h (Fin.last s))|
      ≤ ∑ h : History A (s + 1), |histProb σ h * g i (h (Fin.last s))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h : History A (s + 1), histProb σ h * M := by
        refine Finset.sum_le_sum fun h _ => ?_
        rw [abs_mul, abs_of_nonneg (histProb_nonneg σ h)]
        exact mul_le_mul_of_nonneg_left (hM _ _) (histProb_nonneg σ h)
    _ = M := by rw [← Finset.sum_mul, sum_histProb, one_mul]

theorem summable_payoff (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ) (hw0 : ∀ s, 0 ≤ w s)
    (hw : Summable w) (σ : Profile A) (i : I) :
    Summable (fun s => w s * stageExp g σ i s) := by
  obtain ⟨M, -, hM⟩ := exists_bound g
  refine Summable.of_norm_bounded (hw.mul_right M) fun s => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 s)]
  exact mul_le_mul_of_nonneg_left (abs_stageExp_le g σ i s M hM) (hw0 s)

theorem restrict_nil (σ : Profile A) (h0 : History A 0) : restrict σ h0 = σ := by
  funext i
  have hh0 : h0 = Fin.elim0 := Subsingleton.elim _ _
  subst hh0
  rcases hσ : σ i with ⟨act, hact⟩
  simp only [TimeDepFolk.Asymptotic.restrict, hσ, Fin.elim0_append]
  congr 1
  funext t h'
  have key : ∀ m (e : m = t), act m (h' ∘ Fin.cast e) = act t h' := by
    intro m e; subst e; rfl
  exact key _ (Nat.zero_add t)


theorem act_cast {i : I} (st : Strategy A i) {m m' : ℕ} (e : m = m') (h : History A m') :
    st.act m (h ∘ Fin.cast e) = st.act m' h := by
  subst e; rfl

theorem strategy_ext {i : I} (s1 s2 : Strategy A i) (h : s1.act = s2.act) : s1 = s2 := by
  cases s1; cases s2; simp only at h; subst h; rfl

theorem restrict_restrict (ψ : Profile A) {n n' : ℕ} (h : History A n) (h' : History A n') :
    restrict (restrict ψ h) h' = restrict ψ (Fin.append h h') := by
  funext j
  apply strategy_ext
  funext s h''
  simp only [TimeDepFolk.Asymptotic.restrict]
  rw [Fin.append_assoc]
  exact (act_cast (ψ j) (Nat.add_assoc n n' s) _).symm

theorem take_cons {T : ℕ} (a : ∀ i, A i) (h : History A T) (r : ℕ) (hr : r ≤ T) :
    History.take (Fin.cons a h : History A (T + 1)) (r + 1) (by omega) =
      Fin.cons a (h.take r hr) := by
  funext q
  refine Fin.cases ?_ (fun q' => ?_) q
  · simp only [History.take, Fin.cons_zero]
    have : (Fin.castLE (by omega : r + 1 ≤ T + 1) (0 : Fin (r + 1))) = 0 := by ext; simp
    rw [this, Fin.cons_zero]
  · simp only [History.take, Fin.cons_succ]
    have : (Fin.castLE (by omega : r + 1 ≤ T + 1) q'.succ) =
        (Fin.castLE hr q').succ := by ext; simp
    rw [this, Fin.cons_succ]

/-- The one-stage history `(a)`. -/
def h1 (a : ∀ i, A i) : History A 1 := fun _ => a

/-- First-stage probability of the action profile `a`. -/
noncomputable def P0 (ψ : Profile A) (a : ∀ i, A i) : ℝ :=
  ∏ j, (ψ j).act 0 Fin.elim0 (a j)

theorem P0_nonneg (ψ : Profile A) (a : ∀ i, A i) : 0 ≤ P0 ψ a :=
  Finset.prod_nonneg fun j _ => ((ψ j).act_mem _ _).1 _

theorem histProb_cons (ψ : Profile A) {T : ℕ} (a : ∀ i, A i) (h : History A T) :
    histProb ψ (Fin.cons a h : History A (T + 1)) = P0 ψ a * histProb (restrict ψ (h1 a)) h := by
  unfold histProb P0
  rw [Fin.prod_univ_succ]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Fin.val_zero, Fin.cons_zero]
    congr 1
    exact Subsingleton.elim _ _
  · refine Finset.prod_congr rfl fun r _ => Finset.prod_congr rfl fun j _ => ?_
    simp only [TimeDepFolk.Asymptotic.restrict, Fin.cons_succ, Fin.val_succ]
    rw [show (Fin.append (h1 a) (h.take r (Nat.le_of_lt r.isLt)) : History A (1 + r)) =
        (History.take (Fin.cons a h : History A (T + 1)) (r + 1) (by omega)) ∘
          Fin.cast (Nat.add_comm 1 r) by
      rw [take_cons a h r (Nat.le_of_lt r.isLt), Fin.append_left_eq_cons]; rfl]
    rw [act_cast]

theorem sum_cons {T : ℕ} {M : Type*} [AddCommMonoid M] (f : History A (T + 1) → M) :
    ∑ h : History A (T + 1), f h = ∑ a : (∀ i, A i), ∑ h : History A T, f (Fin.cons a h) := by
  rw [← (Fin.consEquiv (fun _ : Fin (T + 1) => ∀ i, A i)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem stageExp_succ (g : I → (∀ i, A i) → ℝ) (ψ : Profile A) (i : I) (s : ℕ) :
    stageExp g ψ i (s + 1) = ∑ a, P0 ψ a * stageExp g (restrict ψ (h1 a)) i s := by
  unfold stageExp
  rw [sum_cons]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [histProb_cons, mul_assoc]
  congr 2

theorem stageExp_zero (g : I → (∀ i, A i) → ℝ) (ψ : Profile A) (i : I) :
    stageExp g ψ i 0 = ∑ a, P0 ψ a * g i a := by
  unfold stageExp
  rw [sum_cons]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : (Finset.univ : Finset (History A 0)) = {Fin.elim0} := by
    exact Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_univ _, fun h _ => Subsingleton.elim _ _⟩
  rw [this, Finset.sum_singleton, histProb_cons]
  simp [histProb]

theorem cont_nonneg' (w : ℕ → ℝ) (hw0 : ∀ s, 0 ≤ w s) (n s : ℕ) : 0 ≤ cont w n s :=
  div_nonneg (hw0 _) (tsum_nonneg fun r => hw0 _)

theorem summable_shift' (w : ℕ → ℝ) (hw : Summable w) (n : ℕ) :
    Summable (fun r => w (n + r)) := by
  have := (summable_nat_add_iff n).2 hw
  simpa [add_comm] using this

theorem summable_cont (w : ℕ → ℝ) (hw : Summable w) (n : ℕ) : Summable (cont w n) :=
  (summable_shift' w hw n).div_const _

theorem cont_cont (w : ℕ → ℝ) (hw0 : ∀ s, 0 ≤ w s) (hw : Summable w) (n n' : ℕ) :
    cont (cont w n) n' = cont w (n + n') := by
  funext s
  set τ := ∑' r, w (n + r) with hτ
  have hτ0 : 0 ≤ τ := tsum_nonneg fun r => hw0 _
  have hassoc : ∀ r, w (n + (n' + r)) = w (n + n' + r) := fun r => by rw [add_assoc]
  have htail : ∑' r, cont w n (n' + r) = (∑' r, w (n + n' + r)) / τ := by
    simp only [cont, ← hτ, hassoc]
    exact tsum_div_const
  rcases hτ0.eq_or_lt with h0 | hpos
  · -- zero tail: everything vanishes
    have hz : ∀ r, w (n + r) = 0 := by
      intro r
      have := (summable_shift' w hw n).le_tsum r (fun r _ => hw0 _)
      rw [← hτ, ← h0] at this
      exact le_antisymm this (hw0 _)
    simp only [cont, ← hτ, ← h0, div_zero, zero_div]
    rw [show n + n' + s = n + (n' + s) by omega, hz, zero_div]
  · simp only [cont] at htail ⊢
    rw [htail, ← hτ, hassoc, div_div_div_cancel_right₀ hpos.ne']

/-- One-step decomposition of the payoff: stage `0` plus the weighted continuation payoffs. -/
theorem payoff_decomp (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ) (hw0 : ∀ s, 0 ≤ w s)
    (hw : Summable w) (ψ : Profile A) (i : I) :
    payoff g w ψ i = w 0 * (∑ a, P0 ψ a * g i a) +
      (∑' r, w (1 + r)) * ∑ a, P0 ψ a * payoff g (cont w 1) (restrict ψ (h1 a)) i := by
  unfold payoff
  rw [(summable_payoff g w hw0 hw ψ i).tsum_eq_zero_add, stageExp_zero]
  congr 1
  simp only [stageExp_succ, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun a _ => ?_)]
  · refine Finset.sum_congr rfl fun a _ => ?_
    set W := ∑' r, w (1 + r) with hW
    have hW0 : 0 ≤ W := tsum_nonneg fun r => hw0 _
    rcases hW0.eq_or_lt with h0 | hpos
    · have hz : ∀ r, w (1 + r) = 0 := by
        intro r
        have := (summable_shift' w hw 1).le_tsum r (fun r _ => hw0 _)
        rw [← hW, ← h0] at this
        exact le_antisymm this (hw0 _)
      rw [← h0, zero_mul]
      trans ∑' _ : ℕ, (0 : ℝ)
      · exact tsum_congr fun s => by rw [add_comm s 1, hz]; ring
      · simp
    · simp only [cont, ← hW]
      rw [show (∑' s, w (1 + s) / W * stageExp g (restrict ψ (h1 a)) i s) =
          (∑' s, w (1 + s) * stageExp g (restrict ψ (h1 a)) i s) / W by
        rw [← tsum_div_const]; exact tsum_congr fun s => by ring]
      rw [← mul_assoc, mul_comm W, mul_assoc, mul_div_cancel₀ _ hpos.ne', ← tsum_mul_left]
      exact tsum_congr fun s => by rw [add_comm s 1]; ring
  · have := (summable_payoff g (fun r => w (1 + r)) (fun _ => hw0 _) (summable_shift' w hw 1)
      (restrict ψ (h1 a)) i).mul_left (P0 ψ a)
    refine this.congr fun s => ?_
    simp only [add_comm s 1]; ring

/-- Restriction of a single strategy to the subgame after `h`. -/
def restrictS {i : I} (st : Strategy A i) {n : ℕ} (h : History A n) : Strategy A i :=
  ⟨fun s h' => st.act (n + s) (Fin.append h h'), fun _ _ => st.act_mem _ _⟩

theorem restrict_apply (ψ : Profile A) {n : ℕ} (h : History A n) (j : I) :
    restrict ψ h j = restrictS (ψ j) h := rfl

theorem restrict_update (ψ : Profile A) {n : ℕ} (h : History A n) (i : I) (st : Strategy A i) :
    restrict (Function.update ψ i st) h = Function.update (restrict ψ h) i (restrictS st h) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self, restrict_apply]
  · simp only [Function.update_of_ne hj, restrict_apply]

/-- Follow `τ` before stage `N`, then `ρ`. -/
def trunc {i : I} (N : ℕ) (τ ρ : Strategy A i) : Strategy A i :=
  ⟨fun t h => if t < N then τ.act t h else ρ.act t h, fun t h => by
    by_cases ht : t < N
    · simp only [ht, if_true]; exact τ.act_mem t h
    · simp only [ht, if_false]; exact ρ.act_mem t h⟩

theorem trunc_zero {i : I} (τ ρ : Strategy A i) : trunc 0 τ ρ = ρ := by
  apply strategy_ext; funext t h; simp [trunc]

theorem restrictS_trunc {i : I} (N : ℕ) (τ ρ : Strategy A i) (a : ∀ i, A i) :
    restrictS (trunc (N + 1) τ ρ) (h1 a) = trunc N (restrictS τ (h1 a)) (restrictS ρ (h1 a)) := by
  apply strategy_ext; funext t h
  simp only [restrictS, trunc]
  by_cases ht : t < N
  · rw [if_pos (by omega), if_pos ht]
  · rw [if_neg (by omega), if_neg ht]

/-- Replace the stage-`0` behaviour of `ρ` by the lottery `μ`. -/
def rep0 {i : I} (ρ : Strategy A i) (μ : A i → ℝ) (hμ : AGT.IsLottery μ) : Strategy A i :=
  ⟨fun t h => if t = 0 then μ else ρ.act t h, fun t h => by
    by_cases ht : t = 0
    · simp only [ht, if_true]; exact hμ
    · simp only [ht, if_false]; exact ρ.act_mem t h⟩

theorem oneShot_eq (ψ : Profile A) (i : I) (b : A i) :
    oneShot ψ i b = Function.update ψ i (rep0 (ψ i) (Pi.single b 1) (isLottery_pure b)) := rfl

theorem restrictS_rep0 {i : I} (ρ : Strategy A i) (μ : A i → ℝ) (hμ : AGT.IsLottery μ)
    (a : ∀ i, A i) : restrictS (rep0 ρ μ hμ) (h1 a) = restrictS ρ (h1 a) := by
  apply strategy_ext; funext t h
  simp only [restrictS, rep0]
  rw [if_neg (by omega)]

theorem restrict_update_rep0 (ψ : Profile A) (i : I) (μ : A i → ℝ) (hμ : AGT.IsLottery μ)
    (a : ∀ i, A i) :
    restrict (Function.update ψ i (rep0 (ψ i) μ hμ)) (h1 a) = restrict ψ (h1 a) := by
  rw [restrict_update, restrictS_rep0]
  funext j
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self, restrict_apply]
  · simp only [Function.update_of_ne hj]

theorem P0_update (ψ : Profile A) (i : I) (st : Strategy A i) (a : ∀ i, A i) :
    P0 (Function.update ψ i st) a =
      st.act 0 Fin.elim0 (a i) * ∏ j ∈ Finset.univ.erase i, (ψ j).act 0 Fin.elim0 (a j) := by
  unfold P0
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The payoff of a mixed first-stage deviation is the average of the pure one-shot payoffs. -/
theorem payoff_rep0 (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ) (hw0 : ∀ s, 0 ≤ w s)
    (hw : Summable w) (ψ : Profile A) (i : I) (μ : A i → ℝ) (hμ : AGT.IsLottery μ) :
    payoff g w (Function.update ψ i (rep0 (ψ i) μ hμ)) i =
      ∑ b, μ b * payoff g w (oneShot ψ i b) i := by
  simp only [oneShot_eq]
  simp only [payoff_decomp g w hw0 hw, restrict_update_rep0, P0_update]
  simp only [rep0, if_true]
  set Q : (∀ i, A i) → ℝ := fun a => ∏ j ∈ Finset.univ.erase i, (ψ j).act 0 Fin.elim0 (a j)
  set V : (∀ i, A i) → ℝ := fun a => payoff g (cont w 1) (restrict ψ (h1 a)) i
  have key : ∀ a : (∀ i, A i), ∑ b, μ b * (Pi.single b (1 : ℝ) : A i → ℝ) (a i) = μ (a i) := by
    intro a
    rw [Finset.sum_eq_single (a i)]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · simp
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← key a]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← key a]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring

/-- No profitable one-shot deviation in any subgame. -/
def OSD (g : I → (∀ i, A i) → ℝ) (ψ : Profile A) (w : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (h : History A n) (i : I) (a : A i),
    payoff g (cont w n) (oneShot (restrict ψ h) i a) i ≤ payoff g (cont w n) (restrict ψ h) i

theorem OSD_restrict (g : I → (∀ i, A i) → ℝ) (ψ : Profile A) (w : ℕ → ℝ) (hw0 : ∀ s, 0 ≤ w s)
    (hw : Summable w) (hO : OSD g ψ w) {m : ℕ} (h0 : History A m) :
    OSD g (restrict ψ h0) (cont w m) := by
  intro n h i a
  rw [cont_cont w hw0 hw, restrict_restrict]
  exact hO (m + n) (Fin.append h0 h) i a

theorem trunc_le (g : I → (∀ i, A i) → ℝ) :
    ∀ (N : ℕ) (ψ : Profile A) (w : ℕ → ℝ), (∀ s, 0 ≤ w s) → Summable w → cont w 0 = w →
      OSD g ψ w → ∀ (i : I) (τ : Strategy A i),
        payoff g w (Function.update ψ i (trunc N τ (ψ i))) i ≤ payoff g w ψ i := by
  intro N
  induction N with
  | zero =>
    intro ψ w _ _ _ _ i τ
    rw [trunc_zero, Function.update_eq_self]
  | succ N ih =>
    intro ψ w hw0 hw hself hO i τ
    set μ := τ.act 0 Fin.elim0
    have hμ : AGT.IsLottery μ := τ.act_mem 0 Fin.elim0
    set W := ∑' r, w (1 + r)
    have hW : 0 ≤ W := tsum_nonneg fun r => hw0 _
    -- continuation values under `ψ`
    set V : (∀ i, A i) → ℝ := fun a => payoff g (cont w 1) (restrict ψ (h1 a)) i
    have hw1 : cont (cont w 1) 0 = cont w 1 := by rw [cont_cont w hw0 hw]
    have hcont : ∀ a, payoff g (cont w 1)
        (restrict (Function.update ψ i (trunc (N + 1) τ (ψ i))) (h1 a)) i ≤ V a := by
      intro a
      rw [restrict_update, restrictS_trunc]
      have := ih (restrict ψ (h1 a)) (cont w 1) (cont_nonneg' w hw0 1) (summable_cont w hw 1)
        hw1 (OSD_restrict g ψ w hw0 hw hO (h1 a)) i (restrictS τ (h1 a))
      simpa only [restrict_apply] using this
    have hP0 : ∀ a, P0 (Function.update ψ i (trunc (N + 1) τ (ψ i))) a =
        P0 (Function.update ψ i (rep0 (ψ i) μ hμ)) a := by
      intro a
      rw [P0_update, P0_update]
      simp only [trunc, rep0, if_true, Nat.zero_lt_succ, μ]
    calc payoff g w (Function.update ψ i (trunc (N + 1) τ (ψ i))) i
        ≤ w 0 * (∑ a, P0 (Function.update ψ i (rep0 (ψ i) μ hμ)) a * g i a) +
            W * ∑ a, P0 (Function.update ψ i (rep0 (ψ i) μ hμ)) a * V a := by
          rw [payoff_decomp g w hw0 hw]
          simp only [hP0]
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hW)
          refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (P0_nonneg _ a)
          exact hcont a
      _ = payoff g w (Function.update ψ i (rep0 (ψ i) μ hμ)) i := by
          rw [payoff_decomp g w hw0 hw]
          simp only [restrict_update_rep0, V, W]
      _ = ∑ b, μ b * payoff g w (oneShot ψ i b) i := payoff_rep0 g w hw0 hw ψ i μ hμ
      _ ≤ ∑ b, μ b * payoff g w ψ i := by
          refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hμ.1 b)
          have := hO 0 Fin.elim0 i b
          rwa [restrict_nil, hself] at this
      _ = payoff g w ψ i := by rw [← Finset.sum_mul, hμ.2, one_mul]

theorem histProb_agree (ψ1 ψ2 : Profile A) (N : ℕ)
    (hag : ∀ j t, t < N → ∀ h : History A t, (ψ1 j).act t h = (ψ2 j).act t h) :
    ∀ T ≤ N, ∀ h : History A T, histProb ψ1 h = histProb ψ2 h := by
  intro T hT h
  unfold histProb
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun j _ => ?_
  rw [hag j s (by omega)]

theorem payoff_trunc_tendsto (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ) (hw0 : ∀ s, 0 ≤ w s)
    (hw : Summable w) (ψ : Profile A) (i : I) (τ : Strategy A i) :
    Filter.Tendsto (fun N => payoff g w (Function.update ψ i (trunc N τ (ψ i))) i)
      Filter.atTop (nhds (payoff g w (Function.update ψ i τ) i)) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound g
  set ψ1 := Function.update ψ i τ
  set ψN : ℕ → Profile A := fun N => Function.update ψ i (trunc N τ (ψ i))
  have hag : ∀ N j t, t < N → ∀ h : History A t, (ψN N j).act t h = (ψ1 j).act t h := by
    intro N j t ht h
    by_cases hj : j = i
    · subst hj; simp [ψN, ψ1, trunc, ht]
    · simp [ψN, ψ1, Function.update_of_ne hj]
  have hstage : ∀ N s, s < N → stageExp g (ψN N) i s = stageExp g ψ1 i s := by
    intro N s hs
    unfold stageExp
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [histProb_agree (ψN N) ψ1 N (hag N) (s + 1) (by omega) h]
  -- the tail weights vanish
  have htail : Filter.Tendsto (fun N => ∑' r, w (r + N)) Filter.atTop (nhds 0) := by
    have e : ∀ N, ∑' r, w (r + N) = ∑' r, w r - ∑ r ∈ Finset.range N, w r := by
      intro N; rw [← hw.sum_add_tsum_nat_add N]; ring
    simp only [e]
    simpa using (tendsto_const_nhds (x := ∑' r, w r)).sub hw.hasSum.tendsto_sum_nat
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (by simpa using htail.const_mul (2 * M))
  -- bound the difference by the tail weight
  set f : ℕ → ℝ := fun s => w s * stageExp g (ψN N) i s - w s * stageExp g ψ1 i s
  have hf : Summable f :=
    (summable_payoff g w hw0 hw (ψN N) i).sub (summable_payoff g w hw0 hw ψ1 i)
  have hdiff : payoff g w (ψN N) i - payoff g w ψ1 i = ∑' s, f s := by
    unfold payoff
    rw [← (summable_payoff g w hw0 hw (ψN N) i).tsum_sub (summable_payoff g w hw0 hw ψ1 i)]
  have hsplit := hf.sum_add_tsum_nat_add N
  have hzero : ∑ s ∈ Finset.range N, f s = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    simp only [f, hstage N s (Finset.mem_range.1 hs), sub_self]
  have hbound : ∀ s, |f (s + N)| ≤ 2 * M * w (s + N) := by
    intro s
    simp only [f, ← mul_sub, abs_mul, abs_of_nonneg (hw0 _)]
    have h1 := abs_stageExp_le g (ψN N) i (s + N) M hM
    have h2 := abs_stageExp_le g ψ1 i (s + N) M hM
    have : |stageExp g (ψN N) i (s + N) - stageExp g ψ1 i (s + N)| ≤ 2 * M := by
      rw [abs_le] at h1 h2 ⊢; constructor <;> linarith
    nlinarith [hw0 (s + N)]
  have hsw : Summable (fun s => 2 * M * w (s + N)) :=
    ((summable_nat_add_iff N).2 hw).mul_left _
  have hfN : Summable (fun s => f (s + N)) := (summable_nat_add_iff N).2 hf
  rw [Real.norm_eq_abs, hdiff, ← hsplit, hzero, zero_add, abs_le]
  rw [← tsum_mul_left]
  constructor
  · rw [← tsum_neg]
    exact Summable.tsum_le_tsum (fun s => by have := hbound s; rw [abs_le] at this; linarith)
      hsw.neg hfN
  · exact Summable.tsum_le_tsum (fun s => (le_abs_self _).trans (hbound s)) hfN hsw

end TDFAux

open TimeDepFolk.Asymptotic

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (g : I → (∀ i, A i) → ℝ) (θ : Evaluation) (σ : Profile A) :
    IsSPE g θ σ ↔ ∀ (n : ℕ) (h : History A n) (i : I) (a : A i),
      payoff g (cont θ.θ n) (oneShot (restrict σ h) i a) i ≤
        payoff g (cont θ.θ n) (restrict σ h) i := by
  constructor
  · intro hS n h i a
    exact hS n h i _
  · intro hO n h i τ
    have hw0 : ∀ s, 0 ≤ cont θ.θ n s := TDFAux.cont_nonneg' θ.θ θ.nonneg n
    have hw : Summable (cont θ.θ n) := TDFAux.summable_cont θ.θ θ.hasSum.summable n
    have hself : cont (cont θ.θ n) 0 = cont θ.θ n :=
      TDFAux.cont_cont θ.θ θ.nonneg θ.hasSum.summable n 0
    have hOSD : TDFAux.OSD g (restrict σ h) (cont θ.θ n) :=
      TDFAux.OSD_restrict g σ θ.θ θ.nonneg θ.hasSum.summable hO h
    exact le_of_tendsto' (TDFAux.payoff_trunc_tendsto g _ hw0 hw (restrict σ h) i τ)
      (fun N => TDFAux.trunc_le g N (restrict σ h) _ hw0 hw hself hOSD i τ)
