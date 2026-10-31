-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.interior_mem_eqPayoffs
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:54:25.658381+00:00
-- url     : https://prove2.me/submissions/7f2106f0-2d89-4f29-b756-810bbe9887b1

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model
import Theorems.Thm_TimeDepFolk_Asymptotic_one_shot_deviation
import Theorems.Thm_TimeDepFolk_Asymptotic_eq_5_1
import Theorems.Thm_TimeDepFolk_Asymptotic_lemma_4_2

set_option linter.unusedSectionVars false

namespace TDFTail

open TimeDepFolk.Asymptotic Finset

theorem summable_shift (θ : Evaluation) (n : ℕ) : Summable (fun r => θ.θ (n + r)) := by
  have := (summable_nat_add_iff n).2 θ.hasSum.summable
  simpa [add_comm] using this

theorem tail_nonneg (θ : Evaluation) (n : ℕ) : 0 ≤ ∑' r, θ.θ (n + r) :=
  tsum_nonneg fun r => θ.nonneg _

theorem cont_nonneg (θ : Evaluation) (n t : ℕ) : 0 ≤ cont θ.θ n t :=
  div_nonneg (θ.nonneg _) (tail_nonneg θ n)

theorem cont_le_zero (θ : Evaluation) (n t : ℕ) : cont θ.θ n t ≤ cont θ.θ n 0 :=
  div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem cont_antitone (θ : Evaluation) (n : ℕ) : Antitone (cont θ.θ n) :=
  fun _ _ h => div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem hasSum_cont (θ : Evaluation) (n : ℕ) (h : 0 < ∑' r, θ.θ (n + r)) :
    HasSum (cont θ.θ n) 1 := by
  have := ((summable_shift θ n).hasSum).div_const (∑' r, θ.θ (n + r))
  rwa [div_self h.ne'] at this

theorem sum_range_cont (θ : Evaluation) (n m : ℕ) :
    ∑ t ∈ range m, cont θ.θ n t = (∑ t ∈ range m, θ.θ (n + t)) / ∑' r, θ.θ (n + r) := by
  simp only [cont, Finset.sum_div]

theorem tail_split (θ : Evaluation) (n m : ℕ) :
    ∑' r, θ.θ (n + r) = ∑ r ∈ range m, θ.θ (n + r) + ∑' r, θ.θ (n + m + r) := by
  have := (summable_shift θ n).sum_add_tsum_nat_add m
  rw [← this]
  congr 1
  refine tsum_congr fun r => ?_
  congr 1; omega

end TDFTail


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

theorem dep_cast {β : Type*} (F : (n : ℕ) → History A n → β) {m m' : ℕ} (e : m = m')
    (h : History A m') : F m (h ∘ Fin.cast e) = F m' h := by
  subst e; rfl

/-- Probability of the pure profile `a` under independent mixing `μ`. -/
noncomputable def Q (μ : ∀ j, A j → ℝ) (a : ∀ i, A i) : ℝ := ∏ j, μ j (a j)

theorem Q_nonneg (μ : ∀ j, A j → ℝ) (hμ : ∀ j, AGT.IsLottery (μ j)) (a : ∀ i, A i) :
    0 ≤ Q μ a := Finset.prod_nonneg fun j _ => (hμ j).1 _

theorem sum_Q (μ : ∀ j, A j → ℝ) (hμ : ∀ j, AGT.IsLottery (μ j)) : ∑ a, Q μ a = 1 :=
  sum_prob_profile μ hμ

theorem abs_payoff_le (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ) (hw0 : ∀ s, 0 ≤ w s)
    (hw : HasSum w 1) (ψ : Profile A) (i : I) (M : ℝ) (hM : ∀ i a, |g i a| ≤ M) :
    |payoff g w ψ i| ≤ M := by
  unfold payoff
  have hs := summable_payoff g w hw0 hw.summable ψ i
  rw [abs_le]
  have h1 : ∑' s, w s * M = M := by rw [tsum_mul_right, hw.tsum_eq, one_mul]
  have hb : ∀ s, |w s * stageExp g ψ i s| ≤ w s * M := by
    intro s; rw [abs_mul, abs_of_nonneg (hw0 s)]
    exact mul_le_mul_of_nonneg_left (abs_stageExp_le g ψ i s M hM) (hw0 s)
  constructor
  · rw [← h1, ← tsum_neg]
    exact Summable.tsum_le_tsum (fun s => by have := hb s; rw [abs_le] at this; linarith)
      (hw.summable.mul_right M).neg hs
  · rw [← h1]
    exact Summable.tsum_le_tsum (fun s => (le_abs_self _).trans (hb s)) hs
      (hw.summable.mul_right M)

/-- The profile playing the lotteries `α n h` after every history. -/
def stratOf (α : (n : ℕ) → History A n → (∀ j, A j → ℝ))
    (hα : ∀ n h j, AGT.IsLottery (α n h j)) : Profile A :=
  fun j => ⟨fun n h => α n h j, fun n h => hα n h j⟩

theorem P0_restrict_stratOf (α : (n : ℕ) → History A n → (∀ j, A j → ℝ))
    (hα : ∀ n h j, AGT.IsLottery (α n h j)) {n : ℕ} (h : History A n) (a : ∀ i, A i) :
    P0 (restrict (stratOf α hα) h) a = Q (α n h) a := by
  unfold P0 Q
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [TimeDepFolk.Asymptotic.restrict, stratOf, Fin.append_elim0]
  rw [dep_cast (fun m hh => α m hh j (a j)) (Nat.add_zero n) h]

theorem restrict_snoc (ψ : Profile A) {n : ℕ} (h : History A n) (a : ∀ i, A i) :
    restrict (restrict ψ h) (h1 a) = restrict ψ (Fin.snoc h a : History A (n + 1)) := by
  rw [restrict_restrict]
  congr 1
  exact Fin.append_right_eq_snoc h (h1 a)

/-- **Verification lemma** (self-generation): promise keeping, one-shot incentive constraints and
boundedness of the promised values make `stratOf α` a subgame perfect equilibrium whose
continuation payoffs are the promised values. -/
theorem verification [Nonempty I] [∀ i, Nonempty (A i)] (g : I → (∀ i, A i) → ℝ) (θ : Evaluation)
    (hτ : ∀ n, 0 < ∑' r, θ.θ (n + r))
    (α : (n : ℕ) → History A n → (∀ j, A j → ℝ)) (hα : ∀ n h j, AGT.IsLottery (α n h j))
    (V : (n : ℕ) → History A n → I → ℝ) (B : ℝ) (hB : ∀ n h i, |V n h i| ≤ B)
    (hPK : ∀ n (h : History A n) i, V n h i =
      cont θ.θ n 0 * ∑ a, Q (α n h) a * g i a +
        (1 - cont θ.θ n 0) * ∑ a, Q (α n h) a * V (n + 1) (Fin.snoc h a) i)
    (hIC : ∀ n (h : History A n) i (b : A i),
      cont θ.θ n 0 * ∑ a, Q (Function.update (α n h) i (Pi.single b 1)) a * g i a +
        (1 - cont θ.θ n 0) * ∑ a, Q (Function.update (α n h) i (Pi.single b 1)) a *
          V (n + 1) (Fin.snoc h a) i ≤ V n h i) :
    (∀ n (h : History A n) i, payoff g (cont θ.θ n) (restrict (stratOf α hα) h) i = V n h i) ∧
      IsSPE g θ (stratOf α hα) := by
  set σ := stratOf α hα with hσ
  obtain ⟨M, hM0, hM⟩ := exists_bound g
  set τ : ℕ → ℝ := fun n => ∑' r, θ.θ (n + r)
  have hw0 : ∀ n s, 0 ≤ cont θ.θ n s := cont_nonneg' θ.θ θ.nonneg
  have hwsum : ∀ n, HasSum (cont θ.θ n) 1 := by
    intro n
    have := ((summable_shift' θ.θ θ.hasSum.summable n).hasSum).div_const (∑' r, θ.θ (n + r))
    rwa [div_self (hτ n).ne'] at this
  -- `1 - c_n` is the remaining weight
  have hW : ∀ n, ∑' r, cont θ.θ n (1 + r) = 1 - cont θ.θ n 0 := by
    intro n
    have := (hwsum n).summable.tsum_eq_zero_add
    rw [(hwsum n).tsum_eq] at this
    have e : ∑' r, cont θ.θ n (r + 1) = ∑' r, cont θ.θ n (1 + r) :=
      tsum_congr fun r => by rw [add_comm]
    linarith
  have hcc : ∀ n, cont (cont θ.θ n) 1 = cont θ.θ (n + 1) := fun n =>
    cont_cont θ.θ θ.nonneg θ.hasSum.summable n 1
  have hratio : ∀ n, 1 - cont θ.θ n 0 = τ (n + 1) / τ n := by
    intro n
    have h1 := TDFTail.tail_split θ n 1
    simp only [Finset.range_one, Finset.sum_singleton, add_zero] at h1
    have hpos := hτ n
    simp only [cont, add_zero, τ]
    field_simp
    linarith
  -- Step 1: continuation payoffs equal promised values
  set D : (n : ℕ) → History A n → I → ℝ := fun n h i =>
    payoff g (cont θ.θ n) (restrict σ h) i - V n h i with hD
  have hDrec : ∀ n (h : History A n) i, D n h i =
      (1 - cont θ.θ n 0) * ∑ a, Q (α n h) a * D (n + 1) (Fin.snoc h a) i := by
    intro n h i
    simp only [hD]
    rw [payoff_decomp g _ (hw0 n) (hwsum n).summable, hW, hcc, hPK n h i]
    simp only [hσ, P0_restrict_stratOf, restrict_snoc]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hDb : ∀ n (h : History A n) i, |D n h i| ≤ M + B := by
    intro n h i
    have := abs_payoff_le g _ (hw0 n) (hwsum n) (restrict σ h) i M hM
    have := hB n h i
    simp only [hD]
    calc |payoff g (cont θ.θ n) (restrict σ h) i - V n h i|
        ≤ |payoff g (cont θ.θ n) (restrict σ h) i| + |V n h i| := abs_sub _ _
      _ ≤ M + B := add_le_add (by assumption) (by assumption)
  have hiter : ∀ N n (h : History A n) i, |D n h i| ≤ (M + B) * (τ (n + N) / τ n) := by
    intro N
    induction N with
    | zero =>
      intro n h i
      rw [add_zero, div_self (hτ n).ne', mul_one]; exact hDb n h i
    | succ N ih =>
      intro n h i
      rw [hDrec, hratio, abs_mul, abs_of_nonneg (div_nonneg (hτ _).le (hτ _).le)]
      have hsum : |∑ a, Q (α n h) a * D (n + 1) (Fin.snoc h a) i| ≤
          (M + B) * (τ (n + 1 + N) / τ (n + 1)) := by
        calc |∑ a, Q (α n h) a * D (n + 1) (Fin.snoc h a) i|
            ≤ ∑ a, |Q (α n h) a * D (n + 1) (Fin.snoc h a) i| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ a, Q (α n h) a * ((M + B) * (τ (n + 1 + N) / τ (n + 1))) := by
              refine Finset.sum_le_sum fun a _ => ?_
              rw [abs_mul, abs_of_nonneg (Q_nonneg _ (hα n h) a)]
              exact mul_le_mul_of_nonneg_left (ih _ _ i) (Q_nonneg _ (hα n h) a)
          _ = (M + B) * (τ (n + 1 + N) / τ (n + 1)) := by
              rw [← Finset.sum_mul, sum_Q _ (hα n h), one_mul]
      calc τ (n + 1) / τ n * |∑ a, Q (α n h) a * D (n + 1) (Fin.snoc h a) i|
          ≤ τ (n + 1) / τ n * ((M + B) * (τ (n + 1 + N) / τ (n + 1))) :=
            mul_le_mul_of_nonneg_left hsum (div_nonneg (hτ _).le (hτ _).le)
        _ = (M + B) * (τ (n + (N + 1)) / τ n) := by
            rw [show n + (N + 1) = n + 1 + N by omega]
            rw [show τ (n + 1) / τ n * ((M + B) * (τ (n + 1 + N) / τ (n + 1))) =
                (M + B) * (τ (n + 1 + N) / τ n) * (τ (n + 1) / τ (n + 1)) by ring,
              div_self (hτ (n + 1)).ne', mul_one]
  have hτlim : ∀ n, Filter.Tendsto (fun N => τ (n + N)) Filter.atTop (nhds 0) := by
    intro n
    have e : ∀ N, τ (n + N) = τ n - ∑ r ∈ Finset.range N, θ.θ (n + r) := by
      intro N
      have := TDFTail.tail_split θ n N
      simp only [τ]; linarith
    simp only [e]
    have := (summable_shift' θ.θ θ.hasSum.summable n).hasSum.tendsto_sum_nat
    have h2 := (tendsto_const_nhds (x := τ n)).sub this
    simp only [τ, sub_self] at h2 ⊢
    exact h2
  have hstep1 : ∀ n (h : History A n) i,
      payoff g (cont θ.θ n) (restrict σ h) i = V n h i := by
    intro n h i
    have hz : D n h i = 0 := by
      have hlim : Filter.Tendsto (fun N => (M + B) * (τ (n + N) / τ n)) Filter.atTop (nhds 0) := by
        simpa using ((hτlim n).div_const (τ n)).const_mul (M + B)
      have := ge_of_tendsto' hlim (fun N => hiter N n h i)
      exact abs_nonpos_iff.1 this
    simp only [hD] at hz
    linarith
  refine ⟨hstep1, ?_⟩
  -- Step 2: one-shot deviations are unprofitable
  rw [one_shot_deviation]
  intro n h i b
  rw [hstep1, oneShot_eq, payoff_decomp g _ (hw0 n) (hwsum n).summable, hW, hcc]
  simp only [restrict_update_rep0, restrict_snoc, hstep1]
  have hP : ∀ a, P0 (Function.update (restrict σ h) i
      (rep0 (restrict σ h i) (Pi.single b 1) (isLottery_pure b))) a =
      Q (Function.update (α n h) i (Pi.single b 1)) a := by
    intro a
    have e : (fun j => (Function.update (restrict σ h) i
        (rep0 (restrict σ h i) (Pi.single b 1) (isLottery_pure b)) j).act 0 Fin.elim0) =
        Function.update (fun j => (restrict σ h j).act 0 Fin.elim0) i (Pi.single b 1) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [rep0]
      · simp [Function.update_of_ne hj]
    have e2 : (fun j => (restrict σ h j).act 0 Fin.elim0) = α n h := by
      funext j
      simp only [TimeDepFolk.Asymptotic.restrict, σ, stratOf, Fin.append_elim0]
      exact dep_cast (fun m hh => α m hh j) (Nat.add_zero n) h
    unfold P0 Q
    rw [← e2, ← e]
  simp only [hP]
  exact hIC n h i b

/-! ### The equilibrium automaton -/

/-- States of the automaton: a cooperative phase (target weights `p`, current weights `μ`) or
the punishment of `i` started at stage `n0` with promised value `V`. -/
inductive St (I : Type*) (X : Type*) where
  | coop (p μ : X → ℝ)
  | pun (i : I) (n0 : ℕ) (V : I → ℝ)

/-- Tail weight `τ_n = ∑_{s ≥ n} θ_s`. -/
noncomputable def tl (θ : Evaluation) (n : ℕ) : ℝ := ∑' r, θ.θ (n + r)

/-- All the data and estimates used by the construction. -/
structure Cfg (g : I → (∀ i, A i) → ℝ) (θ : Evaluation) where
  M : ℝ
  η : ℝ
  κ : ℝ
  εm : ℝ
  zmax : ℝ
  R : ℝ
  hM0 : 0 < M
  hM : ∀ i a, |g i a| ≤ M
  hη : 0 < η
  hκ0 : 0 < κ
  hεm0 : 0 ≤ εm
  hεm1 : εm ≤ 1
  hεmη : 2 * εm * M ≤ η
  r : I → I → ℝ
  hR : ∀ i j, |r i j| ≤ R
  αP : I → (∀ j, A j → ℝ)
  hαP : ∀ i j, AGT.IsLottery (αP i j)
  u : I → I → ℝ
  hu : ∀ i j, u i j = ∑ a, Q (αP i) a * g j a
  hbr : ∀ i b, ∑ a, Q (Function.update (αP i) i (Pi.single b 1)) a * g i a ≤ u i i
  hgap : ∀ i, κ ≤ r i i - u i i
  hsep : ∀ i j, j ≠ i → r j j + zmax ≤ r i j
  Lp : ℕ → ℕ
  hLp : ∀ n, 0 < Lp n
  hτ : ∀ n, 0 < tl θ n
  hcN : ∀ n, cont θ.θ n 0 * Fintype.card (∀ j, A j) ≤ εm
  hcM : ∀ n, 2 * M * cont θ.θ n 0 ≤ η
  hc2 : ∀ n, cont θ.θ n 0 ≤ 1 / 2
  hβlow : ∀ n, 3 * η ≤ κ * ∑ t ∈ Finset.range (Lp n), cont θ.θ n t
  hβhigh : ∀ n, ∑ t ∈ Finset.range (Lp n), cont θ.θ n t ≤ 1 / 2
  hz : ∀ n, 4 * M * ∑ t ∈ Finset.range (Lp n), cont θ.θ n t ≤ zmax
  bary : (I → ℝ) → (∀ j, A j) → ℝ
  hbary : ∀ i (V : I → ℝ), (∀ j, |V j - r i j| ≤ zmax) →
    (∀ b, 0 ≤ bary V b) ∧ ∑ b, bary V b = 1 ∧ ∀ j, ∑ b, bary V b * g j b = V j

noncomputable def updC' (θ : Evaluation) (n : ℕ) (μ : (∀ j, A j) → ℝ) (a' : ∀ j, A j) : (∀ j, A j) → ℝ :=
  fun b => (μ b - cont θ.θ n 0 * (if b = a' then 1 else 0)) / (1 - cont θ.θ n 0)

def valS (g : I → (∀ i, A i) → ℝ) : St I (∀ j, A j) → I → ℝ
  | .coop _ μ => fun j => ∑ b, μ b * g j b
  | .pun _ _ V => V

namespace Cfg

variable [∀ i, Nonempty (A i)] {g : I → (∀ i, A i) → ℝ} {θ : Evaluation} (C : Cfg g θ)

/-- Weight of a punishment phase started at stage `n`. -/
noncomputable def β (n : ℕ) : ℝ := ∑ t ∈ Finset.range (C.Lp n), cont θ.θ n t

/-- Promised value at the start of the punishment of `i` at stage `n`. -/
noncomputable def Vst (i : I) (n : ℕ) : I → ℝ := fun j => C.β n * C.u i j + (1 - C.β n) * C.r i j

/-- Cooperative action: the profile with the largest slack. -/
noncomputable def pickA (p μ : (∀ j, A j) → ℝ) : ∀ j, A j :=
  (Finite.exists_max (fun b => μ b - (1 - C.εm) * p b)).choose

noncomputable def updP (n : ℕ) (i : I) (V : I → ℝ) (a : ∀ j, A j) : I → ℝ :=
  fun j => (V j - cont θ.θ n 0 * (if j = i then C.u i j else g j a)) / (1 - cont θ.θ n 0)

open Classical in
noncomputable def trans (n : ℕ) : St I (∀ j, A j) → (∀ j, A j) → St I (∀ j, A j)
  | .coop p μ, a =>
    if h : ∃ i, a i ≠ C.pickA p μ i ∧ a = Function.update (C.pickA p μ) i (a i) then
      .pun h.choose (n + 1) (C.Vst h.choose (n + 1))
    else .coop p (updC' θ n μ (C.pickA p μ))
  | .pun i n0 V, a =>
    if n + 1 < n0 + C.Lp n0 then .pun i n0 (C.updP n i V a)
    else .coop (C.bary (C.updP n i V a)) (C.bary (C.updP n i V a))

noncomputable def alphaS : St I (∀ j, A j) → (∀ j, A j → ℝ)
  | .coop p μ => fun j => Pi.single (C.pickA p μ j) 1
  | .pun i _ _ => C.αP i


noncomputable def stateOf (s0 : St I (∀ j, A j)) : (n : ℕ) → History A n → St I (∀ j, A j)
  | 0, _ => s0
  | n + 1, h => C.trans n (stateOf s0 n (Fin.init h)) (h (Fin.last n))

theorem stateOf_snoc (s0 : St I (∀ j, A j)) (n : ℕ) (h : History A n) (a : ∀ j, A j) :
    C.stateOf s0 (n + 1) (Fin.snoc h a : History A (n + 1)) = C.trans n (C.stateOf s0 n h) a := by
  simp only [stateOf, Fin.init_snoc, Fin.snoc_last]

/-- The invariant satisfied by every reachable state at stage `n`. -/
def Valid (n : ℕ) : St I (∀ j, A j) → Prop
  | .coop p μ => (∀ b, 0 ≤ p b) ∧ ∑ b, p b = 1 ∧ ∑ b, μ b = 1 ∧
      (∀ b, (1 - C.εm) * p b ≤ μ b) ∧ (∀ j, C.r j j ≤ ∑ b, p b * g j b)
  | .pun i n0 V => n0 ≤ n ∧ n < n0 + C.Lp n0 ∧ ∃ acc : I → ℝ, acc i = 0 ∧
      (∀ j, |acc j| ≤ 2 * C.M * ∑ s ∈ Finset.Ico n0 n, θ.θ s) ∧
      ∀ j, tl θ n * V j = (∑ s ∈ Finset.Ico n (n0 + C.Lp n0), θ.θ s) * C.u i j +
        tl θ (n0 + C.Lp n0) * C.r i j + acc j

end Cfg

namespace Cfg

variable [∀ i, Nonempty (A i)] {g : I → (∀ i, A i) → ℝ} {θ : Evaluation} (C : Cfg g θ)

include C

theorem c_eq (n : ℕ) : cont θ.θ n 0 = θ.θ n / tl θ n := by simp [cont, tl]

theorem tl_succ (n : ℕ) : tl θ (n + 1) = tl θ n - θ.θ n := by
  have := TDFTail.tail_split θ n 1
  simp only [Finset.range_one, Finset.sum_singleton, add_zero] at this
  simp only [tl]; linarith

theorem c_nonneg (n : ℕ) : 0 ≤ cont θ.θ n 0 := cont_nonneg' θ.θ θ.nonneg n 0

theorem one_sub_c (n : ℕ) : 1 - cont θ.θ n 0 = tl θ (n + 1) / tl θ n := by
  have hpos := C.hτ n
  rw [C.c_eq, C.tl_succ]
  field_simp

theorem one_sub_c_pos (n : ℕ) : 0 < 1 - cont θ.θ n 0 := by linarith [C.hc2 n]

theorem tl_Ico (m n : ℕ) (hmn : m ≤ n) :
    tl θ m = ∑ s ∈ Finset.Ico m n, θ.θ s + tl θ n := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  have := TDFTail.tail_split θ m d
  rw [Finset.sum_Ico_eq_sum_range, show m + d - m = d by omega]
  simp only [tl]; linarith

theorem tl_nonneg (n : ℕ) : 0 ≤ tl θ n := TDFTail.tail_nonneg θ n

theorem β_mul (n : ℕ) : C.β n * tl θ n = ∑ s ∈ Finset.Ico n (n + C.Lp n), θ.θ s := by
  rw [β, Finset.sum_Ico_eq_sum_range, show n + C.Lp n - n = C.Lp n by omega, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  have := C.hτ n
  simp only [cont, tl] at this ⊢
  field_simp

theorem one_sub_β_mul (n : ℕ) : (1 - C.β n) * tl θ n = tl θ (n + C.Lp n) := by
  rw [sub_mul, one_mul, C.β_mul, C.tl_Ico n (n + C.Lp n) (by omega)]; ring

theorem β_nonneg (n : ℕ) : 0 ≤ C.β n :=
  Finset.sum_nonneg fun t _ => cont_nonneg' θ.θ θ.nonneg n t

theorem alphaS_lottery (s : St I (∀ j, A j)) (j : I) : AGT.IsLottery (C.alphaS s j) := by
  cases s with
  | coop p μ => exact isLottery_pure _
  | pun i n0 V => exact C.hαP i j

theorem Q_pure (q a : ∀ j, A j) : Q (fun j => (Pi.single (q j) (1 : ℝ) : A j → ℝ)) a =
    if a = q then 1 else 0 := by
  unfold Q
  by_cases h : a = q
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨j, hj⟩ : ∃ j, a j ≠ q j := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Pi.single_apply, hj])

theorem sum_Q_pure (q : ∀ j, A j) (f : (∀ j, A j) → ℝ) :
    ∑ a, Q (fun j => (Pi.single (q j) (1 : ℝ) : A j → ℝ)) a * f a = f q := by
  rw [Finset.sum_eq_single q (fun b _ hb => by rw [C.Q_pure, if_neg hb, zero_mul]) (by simp),
    C.Q_pure, if_pos rfl, one_mul]

theorem update_pure (q : ∀ j, A j) (i : I) (b : A i) :
    Function.update (fun j => (Pi.single (q j) (1 : ℝ) : A j → ℝ)) i (Pi.single b 1) =
      fun j => (Pi.single (Function.update q i b j) (1 : ℝ) : A j → ℝ) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

end Cfg

namespace Cfg

variable [∀ i, Nonempty (A i)] {g : I → (∀ i, A i) → ℝ} {θ : Evaluation} (C : Cfg g θ)

include C

theorem pick_spec (p μ : (∀ j, A j) → ℝ) (b : ∀ j, A j) :
    μ b - (1 - C.εm) * p b ≤ μ (C.pickA p μ) - (1 - C.εm) * p (C.pickA p μ) :=
  (Finite.exists_max (fun b => μ b - (1 - C.εm) * p b)).choose_spec b

theorem abs_u_le (i j : I) : |C.u i j| ≤ C.M := by
  rw [C.hu]
  calc |∑ a, Q (C.αP i) a * g j a| ≤ ∑ a, |Q (C.αP i) a * g j a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, Q (C.αP i) a * C.M := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [abs_mul, abs_of_nonneg (Q_nonneg _ (C.hαP i) a)]
        exact mul_le_mul_of_nonneg_left (C.hM _ _) (Q_nonneg _ (C.hαP i) a)
    _ = C.M := by rw [← Finset.sum_mul, sum_Q _ (C.hαP i), one_mul]

/-- The cooperative update keeps the weights normalised and the margin. -/
theorem coop_step (n : ℕ) (p μ : (∀ j, A j) → ℝ) (hv : C.Valid n (.coop p μ)) (n' : ℕ) :
    C.Valid n' (.coop p (updC' θ n μ (C.pickA p μ))) := by
  obtain ⟨hp0, hp1, hμ1, hmarg, htar⟩ := hv
  set a' := C.pickA p μ
  set c := cont θ.θ n 0
  have hc1 : 0 < 1 - c := C.one_sub_c_pos n
  have hc0 : 0 ≤ c := C.c_nonneg n
  refine ⟨hp0, hp1, ?_, ?_, htar⟩
  · simp only [updC', ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hμ1, mul_one]
    exact div_self hc1.ne'
  · intro b
    simp only [updC']
    rw [le_div_iff₀ hc1]
    have hεm1 := C.hεm1
    by_cases hb : b = a'
    · rw [if_pos hb, hb]
      -- the chosen profile has slack at least `εm / N ≥ c`
      have hN : (0 : ℝ) < Fintype.card (∀ j, A j) := by exact_mod_cast Fintype.card_pos
      have hs : ∑ l, (μ l - (1 - C.εm) * p l) = C.εm := by
        rw [Finset.sum_sub_distrib, hμ1, ← Finset.mul_sum, hp1]; ring
      have hle := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => C.pick_spec p μ l
      rw [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hle
      have hcN := C.hcN n
      have : c ≤ μ a' - (1 - C.εm) * p a' := by
        by_contra hcon; push Not at hcon; nlinarith
      have := mul_nonneg (mul_nonneg (sub_nonneg.2 hεm1) (hp0 a')) hc0
      nlinarith
    · rw [if_neg hb, mul_zero, sub_zero]
      have := hmarg b
      have := mul_nonneg (mul_nonneg (sub_nonneg.2 hεm1) (hp0 b)) hc0
      nlinarith

theorem coop_close (n : ℕ) (p μ : (∀ j, A j) → ℝ) (hv : C.Valid n (.coop p μ)) (j : I) :
    |∑ b, μ b * g j b - ∑ b, p b * g j b| ≤ C.η := by
  obtain ⟨hp0, hp1, hμ1, hmarg, -⟩ := hv
  set d : (∀ j, A j) → ℝ := fun b => μ b - p b
  have hd0 : ∑ b, d b = 0 := by simp only [d, Finset.sum_sub_distrib, hμ1, hp1, sub_self]
  have hdl : ∀ b, -(C.εm * p b) ≤ d b := fun b => by have := hmarg b; simp only [d]; linarith
  have habs : ∀ b, |d b| ≤ d b + 2 * (C.εm * p b) := by
    intro b
    rcases le_or_gt 0 (d b) with h0 | h0
    · rw [abs_of_nonneg h0]; nlinarith [hp0 b, C.hεm0]
    · rw [abs_of_neg h0]; linarith [hdl b]
  have hsum : ∑ b, |d b| ≤ 2 * C.εm := by
    calc ∑ b, |d b| ≤ ∑ b, (d b + 2 * (C.εm * p b)) := Finset.sum_le_sum fun b _ => habs b
      _ = 2 * C.εm := by rw [Finset.sum_add_distrib, hd0, ← Finset.mul_sum, ← Finset.mul_sum, hp1]; ring
  rw [← Finset.sum_sub_distrib]
  calc |∑ b, (μ b * g j b - p b * g j b)| ≤ ∑ b, |d b| * C.M := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (C.hM _ _) (abs_nonneg _)
    _ = (∑ b, |d b|) * C.M := by rw [Finset.sum_mul]
    _ ≤ 2 * C.εm * C.M := mul_le_mul_of_nonneg_right hsum C.hM0.le
    _ ≤ C.η := C.hεmη

theorem coop_bound (n : ℕ) (p μ : (∀ j, A j) → ℝ) (hv : C.Valid n (.coop p μ)) (j : I) :
    |∑ b, μ b * g j b| ≤ C.M := by
  obtain ⟨hp0, hp1, hμ1, hmarg, -⟩ := hv
  have hμ0 : ∀ b, 0 ≤ μ b := fun b => le_trans (by nlinarith [hp0 b, C.hεm1]) (hmarg b)
  calc |∑ b, μ b * g j b| ≤ ∑ b, |μ b * g j b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, μ b * C.M := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul, abs_of_nonneg (hμ0 b)]
        exact mul_le_mul_of_nonneg_left (C.hM _ _) (hμ0 b)
    _ = C.M := by rw [← Finset.sum_mul, hμ1, one_mul]

/-- The start of a punishment is a valid state. -/
theorem valid_start (i : I) (n : ℕ) : C.Valid n (.pun i n (C.Vst i n)) := by
  refine ⟨le_rfl, by have := C.hLp n; omega, fun _ => 0, rfl, fun j => by simp, fun j => ?_⟩
  simp only [Vst, add_zero]
  rw [mul_add, ← mul_assoc, ← mul_assoc, mul_comm (tl θ n) (C.β n), C.β_mul,
    mul_comm (tl θ n) (1 - C.β n), C.one_sub_β_mul]

end Cfg

namespace Cfg

variable [∀ i, Nonempty (A i)] {g : I → (∀ i, A i) → ℝ} {θ : Evaluation} (C : Cfg g θ)

include C

theorem updP_mul (n : ℕ) (i : I) (V : I → ℝ) (a : ∀ j, A j) (j : I) :
    tl θ (n + 1) * C.updP n i V a j =
      tl θ n * V j - θ.θ n * (if j = i then C.u i j else g j a) := by
  have h1 := C.hτ n
  have h2 := C.hτ (n + 1)
  simp only [updP]
  rw [C.one_sub_c n, C.c_eq n]
  field_simp

theorem pun_step (n : ℕ) (i : I) (n0 : ℕ) (V : I → ℝ) (hv : C.Valid n (.pun i n0 V))
    (hE : n + 1 < n0 + C.Lp n0) (a : ∀ j, A j) :
    C.Valid (n + 1) (.pun i n0 (C.updP n i V a)) := by
  obtain ⟨h0, h1, acc, hacc_i, hacc, hinv⟩ := hv
  refine ⟨by omega, hE, fun j => acc j + θ.θ n * (C.u i j - if j = i then C.u i j else g j a),
    by simp [hacc_i], fun j => ?_, fun j => ?_⟩
  · rw [Finset.sum_Ico_succ_top (by omega), mul_add]
    have hθ0 := θ.nonneg n
    have hd : |C.u i j - if j = i then C.u i j else g j a| ≤ 2 * C.M := by
      have := C.abs_u_le i j
      split_ifs
      · simp; linarith [C.hM0]
      · have := C.hM j a
        rw [abs_le] at *; constructor <;> linarith
    calc |acc j + θ.θ n * (C.u i j - if j = i then C.u i j else g j a)|
        ≤ |acc j| + θ.θ n * |C.u i j - if j = i then C.u i j else g j a| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hθ0]
      _ ≤ 2 * C.M * ∑ s ∈ Finset.Ico n0 n, θ.θ s + 2 * C.M * θ.θ n := by
          have := mul_le_mul_of_nonneg_left hd hθ0
          linarith [hacc j]
  · rw [C.updP_mul, hinv j, Finset.sum_eq_sum_Ico_succ_bot (by omega : n < n0 + C.Lp n0)]
    ring

theorem pun_end (n : ℕ) (i : I) (n0 : ℕ) (V : I → ℝ) (hv : C.Valid n (.pun i n0 V))
    (hE : ¬ n + 1 < n0 + C.Lp n0) (a : ∀ j, A j) :
    (∀ j, |C.updP n i V a j - C.r i j| ≤ C.zmax) ∧ C.updP n i V a i = C.r i i := by
  obtain ⟨h0, h1, acc, hacc_i, hacc, hinv⟩ := hv
  have hn : n + 1 = n0 + C.Lp n0 := by omega
  set E := n0 + C.Lp n0
  have hτE := C.hτ E
  -- `τ_E V' = τ_E r + acc'`
  have key : ∀ j, C.updP n i V a j =
      C.r i j + (acc j + θ.θ n * (C.u i j - if j = i then C.u i j else g j a)) / tl θ E := by
    intro j
    have := C.updP_mul n i V a j
    rw [hinv j, Finset.sum_eq_sum_Ico_succ_bot (by omega : n < E), hn, Finset.Ico_self,
      Finset.sum_empty] at this
    by_cases hj : j = i
    · subst hj; simp only [if_true] at this ⊢; field_simp; linarith
    · simp only [hj, if_false] at this ⊢; field_simp; linarith
  -- the accumulated deviation is small
  have hβ : C.β n0 ≤ 1 / 2 := C.hβhigh n0
  have hz : 4 * C.M * C.β n0 ≤ C.zmax := C.hz n0
  have hβmul := C.β_mul n0
  have h1β := C.one_sub_β_mul n0
  have hβ0 := C.β_nonneg n0
  have hτ0 := C.hτ n0
  have hb : ∀ j, |acc j + θ.θ n * (C.u i j - if j = i then C.u i j else g j a)| ≤
      2 * C.M * ∑ s ∈ Finset.Ico n0 E, θ.θ s := by
    intro j
    have hθ0 := θ.nonneg n
    have hd : |C.u i j - if j = i then C.u i j else g j a| ≤ 2 * C.M := by
      have := C.abs_u_le i j
      split_ifs
      · simp; linarith [C.hM0]
      · have := C.hM j a
        rw [abs_le] at *; constructor <;> linarith
    rw [← hn, Finset.sum_Ico_succ_top (by omega)]
    calc |acc j + θ.θ n * (C.u i j - if j = i then C.u i j else g j a)|
        ≤ |acc j| + θ.θ n * |C.u i j - if j = i then C.u i j else g j a| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hθ0]
      _ ≤ 2 * C.M * ∑ s ∈ Finset.Ico n0 n, θ.θ s + 2 * C.M * θ.θ n := by
          have := mul_le_mul_of_nonneg_left hd hθ0
          linarith [hacc j]
      _ = 2 * C.M * (∑ s ∈ Finset.Ico n0 n, θ.θ s + θ.θ n) := by ring
  constructor
  · intro j
    rw [key, add_sub_cancel_left, abs_div, abs_of_pos hτE, div_le_iff₀ hτE]
    refine (hb j).trans ?_
    -- `2M β τ_{n0} ≤ zmax (1-β) τ_{n0}`
    rw [← hβmul]
    have : tl θ E = (1 - C.β n0) * tl θ n0 := h1β.symm
    rw [this]
    have hM := C.hM0
    have hz0 : 0 ≤ C.zmax := le_trans (by positivity) hz
    have h2 := mul_le_mul_of_nonneg_left (by linarith : (1 / 2 : ℝ) ≤ 1 - C.β n0) hz0
    have : 2 * C.M * C.β n0 ≤ C.zmax * (1 - C.β n0) := by linarith
    have := mul_le_mul_of_nonneg_right this hτ0.le
    linarith
  · rw [key]; simp [hacc_i]

theorem pun_bound (n : ℕ) (i : I) (n0 : ℕ) (V : I → ℝ) (hv : C.Valid n (.pun i n0 V)) (j : I) :
    |V j| ≤ 5 * C.M + C.R := by
  obtain ⟨h0, h1, acc, -, hacc, hinv⟩ := hv
  set E := n0 + C.Lp n0
  have hτn := C.hτ n
  have hsplit := C.tl_Ico n E (by omega)
  have hsplit0 := C.tl_Ico n0 n h0
  have hτE := C.tl_nonneg E
  have hβ : C.β n0 ≤ 1 / 2 := C.hβhigh n0
  have h1β := C.one_sub_β_mul n0
  have hτ0 := C.hτ n0
  have hθsum : 0 ≤ ∑ s ∈ Finset.Ico n E, θ.θ s := Finset.sum_nonneg fun s _ => θ.nonneg s
  -- `τ_{n0} ≤ 2 τ_E ≤ 2 τ_n`
  have hE2 : tl θ n0 ≤ 2 * tl θ E := by
    have : tl θ E = (1 - C.β n0) * tl θ n0 := h1β.symm
    rw [this]
    have := mul_le_mul_of_nonneg_right (by linarith : (1 / 2 : ℝ) ≤ 1 - C.β n0) hτ0.le
    linarith
  have hacc' : |acc j| ≤ 2 * C.M * (2 * tl θ n) := by
    refine (hacc j).trans (mul_le_mul_of_nonneg_left ?_ (by linarith [C.hM0]))
    linarith
  have hu := C.abs_u_le i j
  have hr := C.hR i j
  have hb : |tl θ n * V j| ≤ tl θ n * (5 * C.M + C.R) := by
    rw [hinv j]
    calc |(∑ s ∈ Finset.Ico n E, θ.θ s) * C.u i j + tl θ E * C.r i j + acc j|
        ≤ (∑ s ∈ Finset.Ico n E, θ.θ s) * C.M + tl θ E * C.R + 2 * C.M * (2 * tl θ n) := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) hacc')
          · rw [abs_mul, abs_of_nonneg hθsum]; exact mul_le_mul_of_nonneg_left hu hθsum
          · rw [abs_mul, abs_of_nonneg hτE]; exact mul_le_mul_of_nonneg_left hr hτE
      _ ≤ tl θ n * C.M + tl θ n * C.R + 4 * C.M * tl θ n := by
          have hR0 : 0 ≤ C.R := le_trans (abs_nonneg _) hr
          have := C.hM0
          nlinarith
      _ = tl θ n * (5 * C.M + C.R) := by ring
  rw [abs_mul, abs_of_pos hτn] at hb
  exact le_of_mul_le_mul_left hb hτn

end Cfg

namespace Cfg

variable [∀ i, Nonempty (A i)] {g : I → (∀ i, A i) → ℝ} {θ : Evaluation} (C : Cfg g θ)

include C

theorem trans_coop_onpath (n : ℕ) (p μ : (∀ j, A j) → ℝ) :
    C.trans n (.coop p μ) (C.pickA p μ) = .coop p (updC' θ n μ (C.pickA p μ)) := by
  simp only [trans]
  rw [dif_neg]
  rintro ⟨i, hi, -⟩
  exact hi rfl

theorem trans_coop_dev (n : ℕ) (p μ : (∀ j, A j) → ℝ) (j : I) (b : A j)
    (hb : b ≠ C.pickA p μ j) :
    C.trans n (.coop p μ) (Function.update (C.pickA p μ) j b) = .pun j (n + 1) (C.Vst j (n + 1)) := by
  simp only [trans]
  have hex : ∃ i, Function.update (C.pickA p μ) j b i ≠ C.pickA p μ i ∧
      Function.update (C.pickA p μ) j b =
        Function.update (C.pickA p μ) i (Function.update (C.pickA p μ) j b i) :=
    ⟨j, by simp [hb], by simp⟩
  rw [dif_pos hex]
  have hspec := hex.choose_spec.1
  have hch : hex.choose = j := by
    by_contra hne
    exact hspec (by rw [Function.update_of_ne hne])
  rw [hch]

theorem lottery_update (μ : ∀ j, A j → ℝ) (hμ : ∀ j, AGT.IsLottery (μ j)) (j : I) (b : A j) :
    ∀ l, AGT.IsLottery (Function.update μ j (Pi.single b 1) l) := by
  intro l
  by_cases hl : l = j
  · subst hl; simp only [Function.update_self]; exact isLottery_pure b
  · simp only [Function.update_of_ne hl]; exact hμ l

theorem valid_trans (n : ℕ) (s : St I (∀ j, A j)) (hv : C.Valid n s) (a : ∀ j, A j) :
    C.Valid (n + 1) (C.trans n s a) := by
  cases s with
  | coop p μ =>
    simp only [trans]
    split_ifs with h
    · exact C.valid_start _ _
    · exact C.coop_step n p μ hv (n + 1)
  | pun i n0 V =>
    simp only [trans]
    split_ifs with hE
    · exact C.pun_step n i n0 V hv hE a
    · obtain ⟨hnear, hi⟩ := C.pun_end n i n0 V hv hE a
      obtain ⟨hb0, hb1, hbg⟩ := C.hbary i _ hnear
      refine ⟨hb0, hb1, hb1, fun b => ?_, fun j => ?_⟩
      · have := hb0 b; have := C.hεm0; nlinarith
      · rw [hbg j]
        by_cases hj : j = i
        · subst hj; rw [hi]
        · have h1 := C.hsep i j hj
          have h2 := hnear j
          rw [abs_le] at h2
          linarith [h2.1]

theorem valS_trans_pun (n : ℕ) (i : I) (n0 : ℕ) (V : I → ℝ) (hv : C.Valid n (.pun i n0 V))
    (a : ∀ j, A j) : valS g (C.trans n (.pun i n0 V) a) = C.updP n i V a := by
  simp only [trans]
  split_ifs with hE
  · rfl
  · funext j
    obtain ⟨hnear, -⟩ := C.pun_end n i n0 V hv hE a
    exact (C.hbary i _ hnear).2.2 j

theorem sum_updC (n : ℕ) (μ : (∀ j, A j) → ℝ) (a' : ∀ j, A j) (j : I) :
    ∑ b, updC' θ n μ a' b * g j b =
      (∑ b, μ b * g j b - cont θ.θ n 0 * g j a') / (1 - cont θ.θ n 0) := by
  simp only [updC', div_mul_eq_mul_div, ← Finset.sum_div, sub_mul, Finset.sum_sub_distrib]
  congr 2
  simp only [mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem PK (n : ℕ) (s : St I (∀ j, A j)) (hv : C.Valid n s) (j : I) :
    valS g s j = cont θ.θ n 0 * ∑ a, Q (C.alphaS s) a * g j a +
      (1 - cont θ.θ n 0) * ∑ a, Q (C.alphaS s) a * valS g (C.trans n s a) j := by
  have hc1 := C.one_sub_c_pos n
  cases s with
  | coop p μ =>
    simp only [alphaS]
    rw [C.sum_Q_pure (C.pickA p μ) (fun a => g j a),
      C.sum_Q_pure (C.pickA p μ) (fun a => valS g (C.trans n (.coop p μ) a) j),
      C.trans_coop_onpath]
    simp only [valS]
    rw [C.sum_updC]
    field_simp
    ring
  | pun i n0 V =>
    simp only [alphaS]
    simp only [C.valS_trans_pun n i n0 V hv]
    simp only [valS, updP, mul_div_assoc', ← Finset.sum_div]
    have hQ := sum_Q (C.αP i) (C.hαP i)
    by_cases hj : j = i
    · subst hj
      simp only [if_true, ← Finset.sum_mul, hQ, one_mul]
      rw [C.hu j j]
      field_simp
      ring
    · simp only [hj, if_false, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hQ, one_mul]
      rw [show ∑ a, Q (C.αP i) a * (cont θ.θ n 0 * g j a) =
          cont θ.θ n 0 * ∑ a, Q (C.αP i) a * g j a by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring]
      field_simp
      ring

theorem IC (n : ℕ) (s : St I (∀ j, A j)) (hv : C.Valid n s) (j : I) (b : A j) :
    cont θ.θ n 0 * ∑ a, Q (Function.update (C.alphaS s) j (Pi.single b 1)) a * g j a +
      (1 - cont θ.θ n 0) * ∑ a, Q (Function.update (C.alphaS s) j (Pi.single b 1)) a *
        valS g (C.trans n s a) j ≤ valS g s j := by
  have hc1 := C.one_sub_c_pos n
  have hc0 := C.c_nonneg n
  cases s with
  | coop p μ =>
    simp only [alphaS]
    rw [C.update_pure]
    rw [C.sum_Q_pure _ (fun a => g j a),
      C.sum_Q_pure _ (fun a => valS g (C.trans n (.coop p μ) a) j)]
    by_cases hb : b = C.pickA p μ j
    · subst hb
      rw [Function.update_eq_self]
      have hPK := C.PK n _ hv j
      simp only [alphaS] at hPK
      rw [C.sum_Q_pure _ (fun a => g j a),
        C.sum_Q_pure _ (fun a => valS g (C.trans n (.coop p μ) a) j)] at hPK
      exact hPK.symm.le
    · rw [C.trans_coop_dev n p μ j b hb]
      have hPK := C.PK n _ hv j
      simp only [alphaS] at hPK
      rw [C.sum_Q_pure _ (fun a => g j a),
        C.sum_Q_pure _ (fun a => valS g (C.trans n (.coop p μ) a) j), C.trans_coop_onpath] at hPK
      rw [hPK]
      simp only [valS, Vst]
      -- the continuation value on path is close to the target
      have hv' := C.coop_step n p μ hv (n + 1)
      have hclose := C.coop_close (n + 1) p _ hv' j
      have htar := hv.2.2.2.2 j
      rw [abs_le] at hclose
      -- the punishment start value is low
      have hgap := C.hgap j
      have hβl : 3 * C.η ≤ C.κ * C.β (n + 1) := C.hβlow (n + 1)
      have hβ0 := C.β_nonneg (n + 1)
      have hpun : C.β (n + 1) * C.u j j + (1 - C.β (n + 1)) * C.r j j ≤ C.r j j - 3 * C.η := by
        nlinarith
      have hg1 := C.hM j (Function.update (C.pickA p μ) j b)
      have hg2 := C.hM j (C.pickA p μ)
      rw [abs_le] at hg1 hg2
      have hcM := C.hcM n
      have hc2 := C.hc2 n
      have hη := C.hη
      set W := ∑ b, updC' θ n μ (C.pickA p μ) b * g j b
      have hW : C.r j j - C.η ≤ W := by linarith [hclose.1]
      nlinarith
  | pun i n0 V =>
    simp only [alphaS]
    simp only [C.valS_trans_pun n i n0 V hv]
    simp only [valS, updP]
    have hQ := sum_Q _ (C.lottery_update (C.αP i) (C.hαP i) j b)
    by_cases hj : j = i
    · subst hj
      simp only [if_true, ← Finset.sum_mul, hQ, one_mul]
      have := C.hbr j b
      rw [mul_div_cancel₀ _ hc1.ne']
      nlinarith
    · simp only [hj, if_false]
      have e : ∑ a, Q (Function.update (C.αP i) j (Pi.single b 1)) a *
          ((V j - cont θ.θ n 0 * g j a) / (1 - cont θ.θ n 0)) =
          (V j - cont θ.θ n 0 * ∑ a, Q (Function.update (C.αP i) j (Pi.single b 1)) a * g j a) /
            (1 - cont θ.θ n 0) := by
        set Q' := Q (Function.update (C.αP i) j (Pi.single b 1))
        rw [eq_div_iff hc1.ne', Finset.sum_mul, Finset.mul_sum]
        calc _ = ∑ a, (Q' a * V j - cont θ.θ n 0 * (Q' a * g j a)) :=
              Finset.sum_congr rfl fun a _ => by field_simp
          _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hQ, one_mul]
      rw [e, mul_div_cancel₀ _ hc1.ne']
      linarith

theorem bound (n : ℕ) (s : St I (∀ j, A j)) (hv : C.Valid n s) (j : I) :
    |valS g s j| ≤ 5 * C.M + C.R := by
  have hR0 : 0 ≤ C.R := le_trans (abs_nonneg _) (C.hR j j)
  cases s with
  | coop p μ =>
    have := C.coop_bound n p μ hv j
    simp only [valS]; linarith [C.hM0]
  | pun i n0 V => exact C.pun_bound n i n0 V hv j

end Cfg

namespace Cfg

variable [Nonempty I] [∀ i, Nonempty (A i)] {g : I → (∀ i, A i) → ℝ} {θ : Evaluation}
  (C : Cfg g θ)

include C

theorem valid_stateOf (s0 : St I (∀ j, A j)) (h0 : C.Valid 0 s0) :
    ∀ n (h : History A n), C.Valid n (C.stateOf s0 n h)
  | 0, _ => h0
  | n + 1, h => C.valid_trans n _ (valid_stateOf s0 h0 n (Fin.init h)) _

theorem mem_eqPayoffs (p0 : (∀ j, A j) → ℝ) (h0 : C.Valid 0 (.coop p0 p0)) (x : I → ℝ)
    (hx : ∀ j, ∑ b, p0 b * g j b = x j) : x ∈ eqPayoffs g θ := by
  set s0 : St I (∀ j, A j) := .coop p0 p0
  have hval := C.valid_stateOf s0 h0
  set α : (n : ℕ) → History A n → (∀ j, A j → ℝ) := fun n h => C.alphaS (C.stateOf s0 n h)
  have hα : ∀ n h j, AGT.IsLottery (α n h j) := fun n h j => C.alphaS_lottery _ j
  set V : (n : ℕ) → History A n → I → ℝ := fun n h => valS g (C.stateOf s0 n h)
  have hres := verification g θ C.hτ α hα V (5 * C.M + C.R)
    (fun n h j => C.bound n _ (hval n h) j)
    (fun n h j => by
      simp only [V, α, C.stateOf_snoc]
      exact C.PK n _ (hval n h) j)
    (fun n h j b => by
      simp only [V, α, C.stateOf_snoc]
      exact C.IC n _ (hval n h) j b)
  refine ⟨stratOf α hα, hres.2, fun j => ?_⟩
  have h1 := hres.1 0 Fin.elim0 j
  rw [restrict_nil] at h1
  have hc0 : cont θ.θ 0 = θ.θ := by
    funext s; simp [cont, θ.hasSum.tsum_eq]
  rw [hc0] at h1
  rw [h1]
  simp only [V, stateOf, s0, valS]
  exact hx j

end Cfg

theorem exists_weights {α E : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E] (v : α → E)
    (x : E) (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ p : α → ℝ, (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1 ∧ ∑ a, p a • v a = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw0, hw1, hwx⟩ := hx
  refine ⟨fun a => if a ∈ s then w a else 0, fun a => ?_, ?_, ?_⟩
  · dsimp only; split_ifs with h
    · exact hw0 a h
    · exact le_rfl
  · rw [Finset.sum_ite_mem, Finset.univ_inter, hw1]
  · rw [← hwx, s.affineCombination_eq_linear_combination v w hw1]
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]

end TDFAux

open TimeDepFolk.Asymptotic TDFAux

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (g : I → (∀ i, A i) → ℝ) (hint : (interior (F g)).Nonempty)
    (θ : ℕ → Evaluation) (hθ : IsPatient θ) :
    ∀ x ∈ interior (F g), ∃ K : ℕ, ∀ k ≥ K, x ∈ eqPayoffs g (θ k) := by
  classical
  intro x hx
  -- a closed ball around `x` inside `F`
  obtain ⟨ρ0, hρ0, hball0⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  set ρ := ρ0 / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hball : Metric.closedBall x ρ ⊆ F g :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball0
  have hmemF : ∀ y : I → ℝ, (∀ j, |y j - x j| ≤ ρ) → y ∈ F g := by
    intro y hy
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (pi_norm_le_iff_of_nonneg hρ.le).2 fun j => by rw [Real.norm_eq_abs]; exact hy j
  obtain ⟨M, hM0, hM⟩ := exists_bound g
  set ε := ρ / 4 with hεdef
  have hε : 0 < ε := by positivity
  set κ := ρ / 4 with hκdef
  have hκ : 0 < κ := by positivity
  -- minmax actions
  have hmm : ∀ i, ∃ ν : {μ : ∀ j, A j → ℝ // IsMixed μ},
      (⨆ b : A i, AGT.expectedPayoff g (Function.update ν.1 i (Pi.single b 1)) i) <
        minmax g i + ρ / 4 := by
    intro i
    have : Nonempty {μ : ∀ j, A j → ℝ // IsMixed μ} :=
      ⟨⟨fun j => Pi.single (Classical.arbitrary (A j)) 1, fun j => isLottery_pure _⟩⟩
    exact exists_lt_of_ciInf_lt (by unfold minmax; linarith)
  choose ν hν using hmm
  have hbr0 : ∀ i, ∃ b : A i, ∀ b' : A i,
      AGT.expectedPayoff g (Function.update (ν i).1 i (Pi.single b' 1)) i ≤
        AGT.expectedPayoff g (Function.update (ν i).1 i (Pi.single b 1)) i :=
    fun i => Finite.exists_max _
  choose bstar hbstar using hbr0
  set αP : I → (∀ j, A j → ℝ) := fun i => Function.update (ν i).1 i (Pi.single (bstar i) 1)
  have hαP : ∀ i j, AGT.IsLottery (αP i j) := by
    intro i j
    by_cases hj : j = i
    · subst hj; simp only [αP, Function.update_self]; exact isLottery_pure _
    · simp only [αP, Function.update_of_ne hj]; exact (ν i).2 j
  set u : I → I → ℝ := fun i j => ∑ a, Q (αP i) a * g j a
  have hEQ : ∀ (μ : ∀ j, A j → ℝ) i, AGT.expectedPayoff g μ i = ∑ a, Q μ a * g i a := fun _ _ => rfl
  have hbr : ∀ i b, ∑ a, Q (Function.update (αP i) i (Pi.single b 1)) a * g i a ≤ u i i := by
    intro i b
    simp only [αP, u, Function.update_idem, ← hEQ]
    exact hbstar i b
  -- the individually rational levels
  have hIR : ∀ i, minmax g i ≤ x i - ρ := by
    intro i
    have := (hmemF (Function.update x i (x i - ρ)) (fun j => by
      by_cases hj : j = i
      · subst hj; simp [abs_of_pos hρ]
      · simp [Function.update_of_ne hj]; exact hρ.le)).2 i
    simpa using this
  have hui : ∀ i, u i i ≤ minmax g i + ρ / 4 := by
    intro i
    have h1 : u i i ≤ ⨆ b : A i, AGT.expectedPayoff g (Function.update (ν i).1 i (Pi.single b 1)) i :=
      le_ciSup (f := fun b : A i => AGT.expectedPayoff g (Function.update (ν i).1 i (Pi.single b 1)) i)
        (Set.finite_range _).bddAbove (bstar i)
    linarith [hν i]
  set r : I → I → ℝ := fun i j => if j = i then x j - 2 * ε else x j + ε
  set R : ℝ := ∑ j, |x j| + 2 * ε
  have hR : ∀ i j, |r i j| ≤ R := by
    intro i j
    have hxj : |x j| ≤ ∑ j, |x j| := Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ j)
    simp only [r, R]
    split_ifs
    · calc |x j - 2 * ε| ≤ |x j| + |2 * ε| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_pos (by linarith : (0:ℝ) < 2 * ε)]; linarith
    · calc |x j + ε| ≤ |x j| + |ε| := abs_add_le _ _
        _ ≤ _ := by rw [abs_of_pos hε]; linarith
  have hgap : ∀ i, κ ≤ r i i - u i i := by
    intro i; simp only [r, if_true]; linarith [hIR i, hui i]
  set zmax := ε / 2
  have hsep : ∀ i j, j ≠ i → r j j + zmax ≤ r i j := by
    intro i j hj; simp only [r, if_true, if_neg hj, zmax]; linarith
  -- barycentric weights of feasible points
  set bary : (I → ℝ) → (∀ j, A j) → ℝ := fun V =>
    if h : V ∈ feasible g then (exists_weights (fun a i => g i a) V h).choose else fun _ => 0
  have hbaryF : ∀ V, V ∈ feasible g →
      (∀ b, 0 ≤ bary V b) ∧ ∑ b, bary V b = 1 ∧ ∀ j, ∑ b, bary V b * g j b = V j := by
    intro V hV
    obtain ⟨h0, h1, h2⟩ := (exists_weights (fun a i => g i a) V hV).choose_spec
    simp only [bary, dif_pos hV]
    refine ⟨h0, h1, fun j => ?_⟩
    have := congrFun h2 j
    simpa [Finset.sum_apply] using this
  have hbary : ∀ i (V : I → ℝ), (∀ j, |V j - r i j| ≤ zmax) →
      (∀ b, 0 ≤ bary V b) ∧ ∑ b, bary V b = 1 ∧ ∀ j, ∑ b, bary V b * g j b = V j := by
    intro i V hV
    refine hbaryF V (hmemF V fun j => ?_).1
    have h1 := hV j
    have h2 : |r i j - x j| ≤ 2 * ε := by
      simp only [r]; split_ifs
      · rw [show x j - 2 * ε - x j = -(2 * ε) by ring, abs_neg, abs_of_pos (by positivity)]
      · rw [show x j + ε - x j = ε by ring, abs_of_pos hε]; linarith
    calc |V j - x j| = |(V j - r i j) + (r i j - x j)| := by ring_nf
      _ ≤ |V j - r i j| + |r i j - x j| := abs_add_le _ _
      _ ≤ ρ := by simp only [zmax] at h1; linarith
  -- the smallness parameters
  set η := min (κ / 16) (min (1 / (2 * κ)) (κ * ε / (32 * M)))
  have hη : 0 < η := by positivity
  have hη1 : η ≤ κ / 16 := min_le_left _ _
  have hη2 : η ≤ 1 / (2 * κ) := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ κ * ε / (32 * M) := (min_le_right _ _).trans (min_le_right _ _)
  set εm := min (η / (2 * M)) (1 / 2)
  have hεm0 : 0 < εm := by positivity
  have hεmη : 2 * εm * M ≤ η := by
    have : εm ≤ η / (2 * M) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  set N : ℝ := (Fintype.card (∀ j, A j) : ℝ)
  have hN : 0 < N := by simp only [N]; exact_mod_cast Fintype.card_pos
  set cmax := min (min (εm / N) (η / (2 * M))) (min (1 / 2) (η ^ 2))
  have hcmax : 0 < cmax := by positivity
  -- patience: small first weights and positive tails
  have h42 := (lemma_4_2 θ hθ).1
  rw [Metric.tendstoUniformly_iff] at h42
  obtain ⟨K1, hK1⟩ := Filter.eventually_atTop.1 (h42 cmax hcmax)
  have hθ' := hθ
  rw [IsPatient, Metric.tendstoUniformly_iff] at hθ'
  obtain ⟨K2, hK2⟩ := Filter.eventually_atTop.1 (hθ' (1 / 2) (by norm_num))
  refine ⟨max K1 K2, fun k hk => ?_⟩
  set w := θ k
  have hc : ∀ n, cont w.θ n 0 ≤ cmax := by
    intro n
    have := hK1 k (le_of_max_le_left hk) n
    rw [dist_zero_left, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this.le
  have hwpos : ∀ m, 0 < w.θ (m + 1) := by
    intro m
    have h := hK2 k (le_of_max_le_right hk) m
    rcases (w.nonneg (m + 1)).eq_or_lt with h0 | h0
    · have h0' : (θ k).θ (m + 1) = 0 := h0.symm
      rw [h0', div_zero, dist_zero_right, norm_one] at h; norm_num at h
    · exact h0
  have hτ : ∀ n, 0 < tl w n := by
    intro n
    have h1 := TDFTail.tail_split w n 2
    have h2 := TDFTail.tail_nonneg w (n + 2)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, add_zero] at h1
    have h3 := hwpos n
    have h4 := w.nonneg n
    show 0 < ∑' r, w.θ (n + r)
    linarith
  -- punishment lengths
  have hpl : ∀ n, ∃ L : ℕ, IsPunLength w κ η n L := by
    intro n
    refine eq_5_1 w n κ η hκ hη (by linarith) ?_ (hτ n) ((hc n).trans ?_)
    · calc η ≤ 1 / (2 * κ) := hη2
        _ < 1 / κ := by
          rw [div_lt_div_iff₀ (by positivity) hκ]; linarith
    · exact (min_le_right _ _).trans (min_le_right _ _)
  choose Lf hLf using hpl
  have hβ : ∀ n, 3 * η ≤ κ * ∑ t ∈ Finset.range (Lf n + 1), cont w.θ n t ∧
      ∑ t ∈ Finset.range (Lf n + 1), cont w.θ n t ≤ 1 / 2 ∧
      4 * M * ∑ t ∈ Finset.range (Lf n + 1), cont w.θ n t ≤ zmax := by
    intro n
    obtain ⟨-, h1, h2⟩ := hLf n
    set β := ∑ t ∈ Finset.range (Lf n + 1), cont w.θ n t
    have hβ4 : β * κ < 4 * η := by rwa [lt_div_iff₀ hκ] at h2
    refine ⟨?_, ?_, ?_⟩
    · rw [div_le_iff₀ hκ] at h1; linarith
    · nlinarith
    · -- `4Mβ < 16 M η / κ ≤ ε / 2`
      have h3 : η * (32 * M) ≤ κ * ε := by rwa [le_div_iff₀ (by positivity)] at hη3
      simp only [zmax]
      nlinarith
  let C : Cfg g w :=
    { M := M, η := η, κ := κ, εm := εm, zmax := zmax, R := R
      hM0 := hM0, hM := hM, hη := hη, hκ0 := hκ, hεm0 := hεm0.le
      hεm1 := (min_le_right _ _).trans (by norm_num)
      hεmη := hεmη, r := r, hR := hR, αP := αP, hαP := hαP, u := u, hu := fun _ _ => rfl
      hbr := hbr, hgap := hgap, hsep := hsep, Lp := fun n => Lf n + 1
      hLp := fun n => Nat.succ_pos _, hτ := hτ
      hcN := fun n => by
        have : cont w.θ n 0 ≤ εm / N := (hc n).trans ((min_le_left _ _).trans (min_le_left _ _))
        rwa [le_div_iff₀ hN] at this
      hcM := fun n => by
        have : cont w.θ n 0 ≤ η / (2 * M) := (hc n).trans ((min_le_left _ _).trans (min_le_right _ _))
        rw [le_div_iff₀ (by positivity)] at this; linarith
      hc2 := fun n => (hc n).trans ((min_le_right _ _).trans (min_le_left _ _))
      hβlow := fun n => (hβ n).1
      hβhigh := fun n => (hβ n).2.1
      hz := fun n => (hβ n).2.2
      bary := bary, hbary := hbary }
  -- the cooperative start at `x`
  have hxF : x ∈ feasible g := (interior_subset hx).1
  obtain ⟨hp0, hp1, hpx⟩ := hbaryF x hxF
  refine C.mem_eqPayoffs (bary x) ⟨hp0, hp1, hp1, fun b => ?_, fun j => ?_⟩ x hpx
  · have := hp0 b
    have : C.εm ≤ 1 := C.hεm1
    nlinarith
  · show r j j ≤ ∑ b, bary x b * g j b
    rw [hpx j]
    simp only [r, if_true]; linarith
