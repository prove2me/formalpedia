-- Prove2me | solution 1 for WildeQIT.Feedback.eq_21_123
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T16:13:35.576208+00:00
-- url     : https://prove2.me/submissions/d9fef4a1-64bb-43ba-b929-304b8c3b6f3e

import Mathlib
import Definitions.Def_WildeQIT_channelCode
import Definitions.Def_WildeQIT_Feedback_FeedbackCode_errorProb

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WildeQIT.FeedbackConverse

open Finset WildeQIT WildeQIT.Feedback
/-! ## Product-sum identities on `Fin n → Z` -/

section prodsum
variable {Z : Type} [Fintype Z]

lemma sum_succ_fun (n : ℕ) (f : (Fin (n + 1) → Z) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x : Fin n → Z, f (Fin.cons a x) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Z)) _ _ (fun _ => rfl)).symm

lemma sum_prod_eq (n : ℕ) (f : Fin n → Z → ℝ) :
    ∑ x : Fin n → Z, ∏ i, f i (x i) = ∏ i, ∑ z, f i z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.mul_sum]
    exact congrArg (f 0 a * ·) (ih (fun i => f i.succ))

/-- Marginalising a product measure against a function of one coordinate. -/
lemma marg1 (n : ℕ) (f : Fin n → Z → ℝ) (hf : ∀ j, ∑ z, f j z = 1) (h : Z → ℝ) (i : Fin n) :
    ∑ y : Fin n → Z, (∏ j, f j (y j)) * h (y i) = ∑ z, f i z * h z := by
  have e1 : ∀ y : Fin n → Z, (∏ j, f j (y j)) * h (y i)
      = ∏ j, (f j (y j) * (if j = i then h (y j) else 1)) := by
    intro y
    rw [Finset.prod_mul_distrib]
    simp [Finset.prod_ite_eq']
  simp_rw [e1]
  rw [sum_prod_eq n (fun j z => f j z * (if j = i then h z else 1))]
  have e2 : ∀ j, ∑ z, f j z * (if j = i then h z else 1)
      = if j = i then ∑ z, f i z * h z else 1 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, hf j]
  simp_rw [e2]
  simp [Finset.prod_ite_eq']

end prodsum

/-! ## Gibbs inequality (base 2) -/

lemma term_le (P R : ℝ) (hP : 0 ≤ P) (hR : 0 ≤ R) (hpos : 0 < P → 0 < R) :
    P * Real.logb 2 (R / P) ≤ (R - P) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases hP.eq_or_lt with h0 | hp
  · subst h0
    simp only [zero_mul, sub_zero]
    exact div_nonneg hR hl2.le
  · have hr := hpos hp
    have hlog := Real.log_le_sub_one_of_pos (div_pos hr hp)
    rw [Real.logb, le_div_iff₀ hl2]
    have e1 : P * (Real.log (R / P) / Real.log 2) * Real.log 2 = P * Real.log (R / P) := by
      field_simp
    have e2 : P * (R / P - 1) = R - P := by field_simp
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left hlog hP]

lemma gibbs {ι : Type} [Fintype ι] (P R : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hR : ∀ i, 0 ≤ R i)
    (hpos : ∀ i, 0 < P i → 0 < R i) (hPs : ∑ i, P i = 1) (hRs : ∑ i, R i ≤ 1) :
    ∑ i, P i * Real.logb 2 (R i / P i) ≤ 0 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc ∑ i, P i * Real.logb 2 (R i / P i) ≤ ∑ i, (R i - P i) / Real.log 2 :=
        Finset.sum_le_sum fun i _ => term_le _ _ (hP i) (hR i) (hpos i)
    _ = ((∑ i, R i) - ∑ i, P i) / Real.log 2 := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib]
    _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hl2.le

/-- Pointwise splitting of the Gibbs term. -/
lemma tlem (w q gg M : ℝ) (hw : 0 ≤ w) (hq : 0 < w → 0 < q) (hg : 0 < gg) (hM : 0 < M) :
    w / M * Real.logb 2 (q * gg / M / (w / M))
      = w / M * Real.logb 2 gg - w / M * Real.logb 2 (w / q) := by
  rcases hw.eq_or_lt with h0 | hp
  · subst h0; simp
  · have hq' := hq hp
    have e : q * gg / M / (w / M) = gg / (w / q) := by field_simp
    rw [e, Real.logb_div hg.ne' (div_pos hp hq').ne']
    ring

/-! ## Mutual information of a channel (from the direct part) -/

section mi
variable {α β : Type} [Fintype α] [Fintype β]

noncomputable def Q1 (N : Channel α β) (p : FinDist α) (y : β) : ℝ := ∑ x, p.prob x * (N x).prob y

noncomputable def idens (N : Channel α β) (p : FinDist α) (x : α) (y : β) : ℝ :=
  Real.logb 2 ((N x).prob y / Q1 N p y)

noncomputable def Ip (N : Channel α β) (p : FinDist α) : ℝ :=
  ∑ x, ∑ y, p.prob x * (N x).prob y * idens N p x y

lemma Q1_pos (N : Channel α β) (p : FinDist α) {x : α} {y : β} (hp : 0 < p.prob x)
    (hw : 0 < (N x).prob y) : 0 < Q1 N p y :=
  lt_of_lt_of_le (mul_pos hp hw)
    (Finset.single_le_sum (f := fun a => p.prob a * (N a).prob y)
      (fun a _ => mul_nonneg (p.nonneg a) ((N a).nonneg y)) (Finset.mem_univ x))

lemma Q1_nonneg (N : Channel α β) (p : FinDist α) (y : β) : 0 ≤ Q1 N p y :=
  Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) ((N a).nonneg y)

lemma Q1_sum (N : Channel α β) (p : FinDist α) : ∑ y, Q1 N p y = 1 := by
  unfold Q1
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (N _).sum_eq_one, mul_one]
  exact p.sum_eq_one

lemma mi_eq (N : Channel α β) (p : FinDist α) : Ip N p = mutualInfo (N.joint p) := by
  have hfst : ∀ x, (N.joint p).fst.prob x = p.prob x := fun x => by
    simp only [FinDist.fst_prob, Channel.joint_prob]
    rw [← Finset.mul_sum, (N x).sum_eq_one, mul_one]
  have hsnd : ∀ y, (N.joint p).snd.prob y = Q1 N p y := fun y => by
    simp only [FinDist.snd_prob, Channel.joint_prob, Q1]
  have hterm : ∀ x y, p.prob x * (N x).prob y * idens N p x y
      = p.prob x * (N x).prob y * Real.logb 2 (p.prob x * (N x).prob y / Q1 N p y)
        - p.prob x * (N x).prob y * Real.logb 2 (p.prob x) := by
    intro x y
    by_cases hp : p.prob x = 0
    · simp [hp]
    by_cases hw : (N x).prob y = 0
    · simp [hw]
    have hq := Q1_pos N p (lt_of_le_of_ne (p.nonneg x) (Ne.symm hp))
      (lt_of_le_of_ne ((N x).nonneg y) (Ne.symm hw))
    unfold idens
    rw [mul_div_assoc, Real.logb_mul hp (div_ne_zero hw hq.ne')]
    ring
  have hpl : ∀ x, ∑ y, p.prob x * (N x).prob y * Real.logb 2 (p.prob x)
      = p.prob x * Real.logb 2 (p.prob x) := fun x => by
    rw [← Finset.sum_mul, ← Finset.mul_sum, (N x).sum_eq_one, mul_one]
  unfold mutualInfo entropy condEntropy Ip
  simp only [hfst, hsnd, Channel.joint_prob]
  simp only [hterm, Finset.sum_sub_distrib, hpl]
  ring

/-! ### Boundedness of the mutual information (compactness of the simplex) -/

noncomputable def xl (t : ℝ) : ℝ := t * Real.logb 2 t

lemma continuous_xl : Continuous xl := by
  have h : xl = fun t : ℝ => (t * Real.log t) / Real.log 2 := by
    funext t
    simp only [xl, Real.logb, mul_div_assoc]
  rw [h]
  exact Real.continuous_mul_log.div_const _

lemma condEntropy_eq (q : FinDist (α × β)) :
    condEntropy q = -(∑ x, ∑ y, xl (q.prob (x, y))) + ∑ y, xl (q.snd.prob y) := by
  have hterm : ∀ x y, q.prob (x, y) * Real.logb 2 (q.prob (x, y) / q.snd.prob y)
      = xl (q.prob (x, y)) - q.prob (x, y) * Real.logb 2 (q.snd.prob y) := by
    intro x y
    by_cases h : q.prob (x, y) = 0
    · simp [xl, h]
    · have hpos : 0 < q.prob (x, y) := lt_of_le_of_ne (q.nonneg _) (Ne.symm h)
      have hle : q.prob (x, y) ≤ q.snd.prob y := by
        rw [FinDist.snd_prob]
        exact Finset.single_le_sum (f := fun x' => q.prob (x', y))
          (fun x' _ => q.nonneg (x', y)) (Finset.mem_univ x)
      have hs : q.snd.prob y ≠ 0 := (lt_of_lt_of_le hpos hle).ne'
      rw [Real.logb_div h hs, xl]
      ring
  have hswap : ∑ x, ∑ y, q.prob (x, y) * Real.logb 2 (q.snd.prob y)
      = ∑ y, xl (q.snd.prob y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, xl, FinDist.snd_prob]
  unfold condEntropy
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [hswap]
  ring

noncomputable def F (N : Channel α β) (f : α → ℝ) : ℝ :=
  -(∑ x, xl (f x)) + ∑ x, ∑ y, xl (f x * (N x).prob y) - ∑ y, xl (∑ x, f x * (N x).prob y)

lemma mutualInfo_joint_eq (N : Channel α β) (p : FinDist α) :
    mutualInfo (N.joint p) = F N p.prob := by
  have hfst : (N.joint p).fst.prob = p.prob := by
    funext x
    simp only [FinDist.fst_prob, Channel.joint_prob]
    rw [← Finset.mul_sum, (N x).sum_eq_one, mul_one]
  unfold mutualInfo entropy
  rw [condEntropy_eq]
  simp only [hfst, F, xl, FinDist.snd_prob, Channel.joint_prob]
  ring

lemma continuous_F (N : Channel α β) : Continuous (F N) := by
  unfold F
  have hg := continuous_xl
  refine ((continuous_finset_sum _ fun x _ => hg.comp (continuous_apply x)).neg.add
    (continuous_finset_sum _ fun x _ => continuous_finset_sum _ fun y _ =>
      hg.comp ((continuous_apply x).mul continuous_const))).sub
    (continuous_finset_sum _ fun y _ => hg.comp
      (continuous_finset_sum _ fun x _ => (continuous_apply x).mul continuous_const))

def simplex (α : Type) [Fintype α] : Set (α → ℝ) := {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

lemma isCompact_simplex : IsCompact (simplex α) := by
  have hcl : IsClosed (simplex α) := by
    have h1 : IsClosed {f : α → ℝ | ∀ x, 0 ≤ f x} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)
    have h2 : IsClosed {f : α → ℝ | ∑ x, f x = 1} :=
      isClosed_eq (continuous_finset_sum _ fun x _ => continuous_apply x) continuous_const
    exact h1.inter h2
  refine (isCompact_Icc (a := (0 : α → ℝ)) (b := 1)).of_isClosed_subset hcl ?_
  intro f hf
  refine ⟨fun x => hf.1 x, fun x => ?_⟩
  have := Finset.single_le_sum (f := f) (fun y _ => hf.1 y) (Finset.mem_univ x)
  simpa [hf.2] using this

lemma simplex_nonempty [Nonempty α] : (simplex α).Nonempty := by
  refine ⟨fun _ => 1 / (Fintype.card α : ℝ), fun _ => by positivity, ?_⟩
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

lemma bdd [Nonempty α] (N : Channel α β) :
    BddAbove {I : ℝ | ∃ p : FinDist α, I = mutualInfo (N.joint p)} := by
  obtain ⟨f0, _, hmax⟩ :=
    isCompact_simplex.exists_isMaxOn simplex_nonempty (continuous_F N).continuousOn
  refine ⟨F N f0, ?_⟩
  rintro I ⟨p, rfl⟩
  rw [mutualInfo_joint_eq]
  exact hmax ⟨p.nonneg, p.sum_eq_one⟩

end mi

/-! ## Causal kernels: the output law of a feedback code -/

section causal
variable {β : Type} [Fintype β]

/-- Weight of an output word under causal kernels `K i (past) (current)`. -/
noncomputable def Wk {n : ℕ} (K : (i : Fin n) → (Fin i → β) → β → ℝ) (y : Fin n → β) : ℝ :=
  ∏ i, K i (pastOutputs y i) (y i)

/-- Restriction of causal kernels of length `n+1` to the first `n` times. -/
def Kr {n : ℕ} (K : (i : Fin (n + 1)) → (Fin i → β) → β → ℝ) :
    (i : Fin n) → (Fin i → β) → β → ℝ :=
  fun i => K (Fin.castSucc i)

lemma sum_snoc {n : ℕ} (f : (Fin (n + 1) → β) → ℝ) :
    ∑ y, f y = ∑ z : Fin n → β, ∑ b, f (Fin.snoc z b) := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ => β)) _ _ (fun _ => rfl)).symm

lemma past_snoc_castSucc {n : ℕ} (z : Fin n → β) (b : β) (i : Fin n) :
    pastOutputs (Fin.snoc z b : Fin (n + 1) → β) (Fin.castSucc i) = pastOutputs z i := by
  funext j
  simp only [pastOutputs]
  have h : (Fin.castLE (Fin.castSucc i).isLt.le j : Fin (n + 1))
      = Fin.castSucc (Fin.castLE i.isLt.le j) := Fin.ext rfl
  rw [h, Fin.snoc_castSucc]

lemma past_snoc_last {n : ℕ} (z : Fin n → β) (b : β) :
    pastOutputs (Fin.snoc z b : Fin (n + 1) → β) (Fin.last n) = z := by
  funext j
  simp only [pastOutputs]
  have h : (Fin.castLE (Fin.last n).isLt.le j : Fin (n + 1)) = Fin.castSucc j := Fin.ext rfl
  rw [h, Fin.snoc_castSucc]

lemma Wk_snoc {n : ℕ} (K : (i : Fin (n + 1)) → (Fin i → β) → β → ℝ) (z : Fin n → β) (b : β) :
    Wk K (Fin.snoc z b) = Wk (Kr K) z * K (Fin.last n) z b := by
  unfold Wk Kr
  rw [Fin.prod_univ_castSucc]
  simp only [past_snoc_castSucc, past_snoc_last, Fin.snoc_castSucc, Fin.snoc_last]

lemma Wk_sum {n : ℕ} (K : (i : Fin n) → (Fin i → β) → β → ℝ) (hK : ∀ i z, ∑ b, K i z b = 1) :
    ∑ y, Wk K y = 1 := by
  induction n with
  | zero => simp [Wk]
  | succ n ih =>
    rw [sum_snoc]
    simp_rw [Wk_snoc, ← Finset.mul_sum, hK, mul_one]
    exact ih (Kr K) (fun i z => hK _ _)

/-- **Causality**: the output at time `i` may be integrated against the kernel at time `i`. -/
lemma causal {n : ℕ} (K : (i : Fin n) → (Fin i → β) → β → ℝ) (hK : ∀ i z, ∑ b, K i z b = 1)
    (i : Fin n) (h : (Fin i → β) → β → ℝ) :
    ∑ y, Wk K y * h (pastOutputs y i) (y i)
      = ∑ y, Wk K y * ∑ b, K i (pastOutputs y i) b * h (pastOutputs y i) b := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [sum_snoc, sum_snoc]
    simp_rw [Wk_snoc]
    cases i using Fin.lastCases with
    | last =>
      simp_rw [past_snoc_last, Fin.snoc_last]
      refine Finset.sum_congr rfl fun z _ => ?_
      have e1 : ∑ b, Wk (Kr K) z * K (Fin.last n) z b * h z b
          = Wk (Kr K) z * ∑ b, K (Fin.last n) z b * h z b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      have e2 : ∑ b, Wk (Kr K) z * K (Fin.last n) z b * (∑ b', K (Fin.last n) z b' * h z b')
          = Wk (Kr K) z * ∑ b, K (Fin.last n) z b * h z b := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hK, mul_one]
      rw [e1, e2]
    | cast i' =>
      simp_rw [past_snoc_castSucc, Fin.snoc_castSucc]
      have red : ∀ (z : Fin n → β) (X : ℝ),
          ∑ b, Wk (Kr K) z * K (Fin.last n) z b * X = Wk (Kr K) z * X := by
        intro z X
        rw [← Finset.sum_mul, ← Finset.mul_sum, hK, mul_one]
      simp_rw [red]
      exact ih (Kr K) (fun i z => hK _ _) i' h

end causal

/-! ## The code-induced input distributions and the key inequality -/

section code
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def Kc (N : Channel α β) {n M : ℕ} (c : FeedbackCode α β n M) (m : Fin M) :
    (i : Fin n) → (Fin i → β) → β → ℝ :=
  fun i z b => (N (c.enc m i z)).prob b

lemma op_nonneg (N : Channel α β) {n M : ℕ} (c : FeedbackCode α β n M) (m : Fin M)
    (y : Fin n → β) : 0 ≤ c.outputProb N m y :=
  Finset.prod_nonneg fun i _ => (N _).nonneg _

lemma op_sum (N : Channel α β) {n M : ℕ} (c : FeedbackCode α β n M) (m : Fin M) :
    ∑ y, c.outputProb N m y = 1 :=
  Wk_sum (Kc N c m) (fun i z => (N (c.enc m i z)).sum_eq_one)

lemma fac_pos (N : Channel α β) {n M : ℕ} (c : FeedbackCode α β n M) (m : Fin M)
    (y : Fin n → β) (hW : 0 < c.outputProb N m y) (i : Fin n) :
    0 < (N (c.enc m i (pastOutputs y i))).prob (y i) := by
  refine lt_of_le_of_ne ((N _).nonneg _) (fun h => hW.ne' ?_)
  unfold FeedbackCode.outputProb
  exact Finset.prod_eq_zero (Finset.mem_univ i) h.symm

/-- The distribution of the `i`-th channel input under a uniform message and the feedback. -/
noncomputable def pcF {n M : ℕ} (hM : 0 < M) (N : Channel α β) (c : FeedbackCode α β n M)
    (i : Fin n) : FinDist α where
  prob a := ∑ m, ∑ y, if c.enc m i (pastOutputs y i) = a then c.outputProb N m y / M else 0
  nonneg a := Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun y _ => by
    split_ifs
    · exact div_nonneg (op_nonneg N c m y) (Nat.cast_nonneg _)
    · exact le_refl 0
  sum_eq_one := by
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [Finset.sum_comm]
    have e : ∀ m : Fin M, ∑ a, ∑ y, (if c.enc m i (pastOutputs y i) = a
        then c.outputProb N m y / M else 0) = 1 / M := by
      intro m
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Finset.sum_div, op_sum]
    rw [Finset.sum_congr rfl fun m _ => e m]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

lemma pcF_prob {n M : ℕ} (hM : 0 < M) (N : Channel α β) (c : FeedbackCode α β n M) (i : Fin n)
    (a : α) : (pcF hM N c i).prob a
      = ∑ m, ∑ y, if c.enc m i (pastOutputs y i) = a then c.outputProb N m y / M else 0 := rfl

lemma pcF_sum {n M : ℕ} (hM : 0 < M) (N : Channel α β) (c : FeedbackCode α β n M) (i : Fin n)
    (G : α → ℝ) :
    ∑ a, (pcF hM N c i).prob a * G a
      = ∑ m, (1 / M : ℝ) * ∑ y, c.outputProb N m y * G (c.enc m i (pastOutputs y i)) := by
  simp only [pcF_prob, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

lemma pcF_pos {n M : ℕ} (hM : 0 < M) (N : Channel α β) (c : FeedbackCode α β n M) (i : Fin n)
    (m : Fin M) (y : Fin n → β) (hW : 0 < c.outputProb N m y) :
    0 < (pcF hM N c i).prob (c.enc m i (pastOutputs y i)) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hnn : ∀ (m' : Fin M) (y' : Fin n → β), 0 ≤ (if c.enc m' i (pastOutputs y' i)
      = c.enc m i (pastOutputs y i) then c.outputProb N m' y' / M else 0) := by
    intro m' y'
    split_ifs
    · exact div_nonneg (op_nonneg N c m' y') hMr.le
    · exact le_refl 0
  have h1 : 0 < c.outputProb N m y / M := div_pos hW hMr
  refine lt_of_lt_of_le h1 ?_
  rw [pcF_prob]
  have hin := Finset.single_le_sum (f := fun y' => if c.enc m i (pastOutputs y' i)
      = c.enc m i (pastOutputs y i) then c.outputProb N m y' / M else 0)
    (fun y' _ => hnn m y') (Finset.mem_univ y)
  simp only [if_true] at hin
  refine hin.trans ?_
  exact Finset.single_le_sum (f := fun m' => ∑ y', if c.enc m' i (pastOutputs y' i)
      = c.enc m i (pastOutputs y i) then c.outputProb N m' y' / M else 0)
    (fun m' _ => Finset.sum_nonneg fun y' _ => hnn m' y') (Finset.mem_univ m)

lemma Ip_pcF (N : Channel α β) {n M : ℕ} (hM : 0 < M) (c : FeedbackCode α β n M) (i : Fin n) :
    Ip N (pcF hM N c i) = ∑ m, (1 / M : ℝ) * ∑ y, c.outputProb N m y *
      ∑ b, (N (c.enc m i (pastOutputs y i))).prob b *
        Real.logb 2 ((N (c.enc m i (pastOutputs y i))).prob b / Q1 N (pcF hM N c i) b) := by
  unfold Ip idens
  have e : ∀ a, ∑ b, (pcF hM N c i).prob a * (N a).prob b *
        Real.logb 2 ((N a).prob b / Q1 N (pcF hM N c i) b)
      = (pcF hM N c i).prob a * ∑ b, (N a).prob b *
        Real.logb 2 ((N a).prob b / Q1 N (pcF hM N c i) b) := by
    intro a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp_rw [e]
  exact pcF_sum hM N c i _

/-- The product output distribution `∏ᵢ q_i(yᵢ)`. -/
noncomputable def Qn (N : Channel α β) {n M : ℕ} (hM : 0 < M) (c : FeedbackCode α β n M)
    (y : Fin n → β) : ℝ :=
  ∏ i, Q1 N (pcF hM N c i) (y i)

lemma Qn_pos (N : Channel α β) {n M : ℕ} (hM : 0 < M) (c : FeedbackCode α β n M) (m : Fin M)
    (y : Fin n → β) (hW : 0 < c.outputProb N m y) : 0 < Qn N hM c y :=
  Finset.prod_pos fun i _ => Q1_pos N _ (pcF_pos hM N c i m y hW) (fac_pos N c m y hW i)

lemma logsplit (N : Channel α β) {n M : ℕ} (hM : 0 < M) (c : FeedbackCode α β n M) (m : Fin M)
    (y : Fin n → β) :
    c.outputProb N m y * Real.logb 2 (c.outputProb N m y / Qn N hM c y)
    = c.outputProb N m y * ∑ i, Real.logb 2 ((N (c.enc m i (pastOutputs y i))).prob (y i)
        / Q1 N (pcF hM N c i) (y i)) := by
  rcases (op_nonneg N c m y).eq_or_lt with h0 | hW
  · rw [← h0]; simp
  · have hf := fac_pos N c m y hW
    have hq : ∀ i, Q1 N (pcF hM N c i) (y i) ≠ 0 := fun i =>
      (Q1_pos N _ (pcF_pos hM N c i m y hW) (hf i)).ne'
    congr 1
    unfold FeedbackCode.outputProb Qn
    rw [← Finset.prod_div_distrib]
    unfold Real.logb
    rw [Real.log_prod (fun i _ => div_ne_zero (hf i).ne' (hq i)), Finset.sum_div]

lemma code_LHS (N : Channel α β) {n M : ℕ} (hM : 0 < M) (c : FeedbackCode α β n M) (m : Fin M) :
    ∑ y, c.outputProb N m y * Real.logb 2 (c.outputProb N m y / Qn N hM c y)
    = ∑ i, ∑ y, c.outputProb N m y * ∑ b, (N (c.enc m i (pastOutputs y i))).prob b *
        Real.logb 2 ((N (c.enc m i (pastOutputs y i))).prob b / Q1 N (pcF hM N c i) b) := by
  rw [Finset.sum_congr rfl fun y _ => logsplit N hM c m y]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (causal (Kc N c m) (fun i z => (N (c.enc m i z)).sum_eq_one) i
    (fun z b => Real.logb 2 ((N (c.enc m i z)).prob b / Q1 N (pcF hM N c i) b))).trans ?_
  simp only [Finset.mul_sum]
  rfl

/-- The decoding weight: `M/2` on the decoded message, `1/2` elsewhere. -/
noncomputable def gc {n M : ℕ} (c : FeedbackCode α β n M) (m : Fin M) (y : Fin n → β) : ℝ :=
  1 / 2 + if c.dec y = m then ((M : ℝ) - 1) / 2 else 0

lemma logb_gc {n M : ℕ} (hM : 0 < M) (c : FeedbackCode α β n M) (m : Fin M) (y : Fin n → β) :
    Real.logb 2 (gc c m y) = -1 + if c.dec y = m then Real.logb 2 M else 0 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold gc
  split_ifs
  · rw [show (1 / 2 + ((M : ℝ) - 1) / 2) = (M : ℝ) / 2 by ring,
      Real.logb_div hM' two_ne_zero, Real.logb_self_eq_one one_lt_two]
    ring
  · rw [add_zero, one_div, Real.logb_inv, Real.logb_self_eq_one one_lt_two]
    ring

/-- **Key inequality** (Gibbs + causality): `(1-ε) log₂ M - 1 ≤ ∑ᵢ I(Xᵢ;Yᵢ)`. -/
lemma key (N : Channel α β) {n M : ℕ} (hM : 0 < M) (c : FeedbackCode α β n M) {ε : ℝ}
    (herr : c.errorProb N ≤ ε) :
    (1 - ε) * Real.logb 2 M - 1 ≤ ∑ i, Ip N (pcF hM N c i) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hW0 : ∀ m y, 0 ≤ c.outputProb N m y := op_nonneg N c
  have hW1 : ∀ m, ∑ y, c.outputProb N m y = 1 := op_sum N c
  have hQ0 : ∀ y, 0 ≤ Qn N hM c y := fun y =>
    Finset.prod_nonneg fun i _ => Q1_nonneg N _ _
  have hQ1 : ∑ y, Qn N hM c y = 1 :=
    (sum_prod_eq n (fun i z => Q1 N (pcF hM N c i) z)).trans (by simp [Q1_sum])
  have hQpos : ∀ m y, 0 < c.outputProb N m y → 0 < Qn N hM c y := Qn_pos N hM c
  have hg0 : ∀ m y, 0 < gc c m y := by
    intro m y
    unfold gc
    split_ifs
    · have : (0 : ℝ) ≤ ((M : ℝ) - 1) / 2 := by linarith
      linarith
    · norm_num
  have hgs : ∀ y, ∑ m, gc c m y ≤ M := by
    intro y
    unfold gc
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    linarith
  have hG := gibbs (fun z : Fin M × (Fin n → β) => c.outputProb N z.1 z.2 / M)
    (fun z => Qn N hM c z.2 * gc c z.1 z.2 / M)
    (fun z => div_nonneg (hW0 _ _) hMr.le)
    (fun z => div_nonneg (mul_nonneg (hQ0 _) (hg0 _ _).le) hMr.le)
    (fun z hz => div_pos (mul_pos (hQpos _ _ ((div_pos_iff_of_pos_right hMr).1 hz)) (hg0 _ _)) hMr)
    (by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.sum_div, hW1]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp)
    (by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine le_trans (Finset.sum_le_sum fun y _ => ?_) hQ1.le
      have hq := hQ0 y
      calc ∑ m, Qn N hM c y * gc c m y / M = Qn N hM c y * (∑ m, gc c m y) / M := by
            rw [Finset.mul_sum, Finset.sum_div]
        _ ≤ Qn N hM c y * M / M := by gcongr; exact hgs y
        _ = Qn N hM c y := by field_simp)
  rw [Finset.sum_congr rfl fun z _ => tlem _ _ _ _ (hW0 z.1 z.2) (hQpos z.1 z.2) (hg0 z.1 z.2) hMr,
    Finset.sum_sub_distrib] at hG
  have hA : ∑ z : Fin M × (Fin n → β), c.outputProb N z.1 z.2 / M *
      Real.logb 2 (c.outputProb N z.1 z.2 / Qn N hM c z.2) = ∑ i, Ip N (pcF hM N c i) := by
    have h1 : ∀ m, ∑ y, c.outputProb N m y / M *
        Real.logb 2 (c.outputProb N m y / Qn N hM c y)
        = ∑ i, (1 / M : ℝ) * ∑ y, c.outputProb N m y *
          ∑ b, (N (c.enc m i (pastOutputs y i))).prob b *
          Real.logb 2 ((N (c.enc m i (pastOutputs y i))).prob b / Q1 N (pcF hM N c i) b) := by
      intro m
      rw [← Finset.mul_sum, ← code_LHS N hM c m, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    simp only [Fintype.sum_prod_type, h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (Ip_pcF N hM c i).symm
  have hcorr : ∀ m, ∑ y, (if c.dec y = m then c.outputProb N m y else 0)
      = 1 - ∑ y, (if c.dec y = m then 0 else c.outputProb N m y) := by
    intro m
    rw [← hW1 m, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
  have hlogM : 0 ≤ Real.logb 2 M := Real.logb_nonneg one_lt_two hM1
  have hE : c.errorProb N
      = (1 / M : ℝ) * ∑ m, ∑ y, (if c.dec y = m then 0 else c.outputProb N m y) := rfl
  have hB : (1 - ε) * Real.logb 2 M - 1 ≤ ∑ z : Fin M × (Fin n → β),
      c.outputProb N z.1 z.2 / M * Real.logb 2 (gc c z.1 z.2) := by
    have e : ∀ z : Fin M × (Fin n → β), c.outputProb N z.1 z.2 / M * Real.logb 2 (gc c z.1 z.2)
        = -(c.outputProb N z.1 z.2 / M) + Real.logb 2 M *
          ((1 / M : ℝ) * if c.dec z.2 = z.1 then c.outputProb N z.1 z.2 else 0) := by
      intro z
      rw [logb_gc hM]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun z _ => e z, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum]
    have hP1 : ∑ z : Fin M × (Fin n → β), c.outputProb N z.1 z.2 / M = 1 := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.sum_div, hW1]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hS : 1 - ε ≤ ∑ z : Fin M × (Fin n → β),
        (1 / M : ℝ) * (if c.dec z.2 = z.1 then c.outputProb N z.1 z.2 else 0) := by
      have e2 : ∑ z : Fin M × (Fin n → β),
          (1 / M : ℝ) * (if c.dec z.2 = z.1 then c.outputProb N z.1 z.2 else 0)
          = ∑ m : Fin M, ((1 / M : ℝ) - (1 / M : ℝ) *
              ∑ y, (if c.dec y = m then 0 else c.outputProb N m y)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← Finset.mul_sum, hcorr m]
        ring
      rw [e2, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hE]
      have h1 : ∑ _m : Fin M, (1 / M : ℝ) = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      rw [h1]
      linarith
    rw [hP1]
    nlinarith [mul_le_mul_of_nonneg_left hS hlogM]
  linarith

end code

theorem main {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (N : Channel α β) {n M : ℕ} (c : FeedbackCode α β n M) (hM : 0 < M) (ε : ℝ)
    (hε : c.errorProb N ≤ ε) :
    Real.logb 2 M ≤ n * channelMaxMutualInfo N + 1 + ε * Real.logb 2 M := by
  classical
  have hk := key N hM c hε
  have hI : ∀ i, Ip N (pcF hM N c i) ≤ channelMaxMutualInfo N := by
    intro i
    have : Nonempty α := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := (pcF hM N c i).sum_eq_one
      simp at this
    rw [mi_eq]
    exact le_csSup (bdd N) ⟨_, rfl⟩
  have hsum : ∑ i, Ip N (pcF hM N c i) ≤ n * channelMaxMutualInfo N := by
    calc ∑ i, Ip N (pcF hM N c i) ≤ ∑ _i : Fin n, channelMaxMutualInfo N :=
          Finset.sum_le_sum fun i _ => hI i
      _ = n * channelMaxMutualInfo N := by simp
  linarith

end WildeQIT.FeedbackConverse

open WildeQIT WildeQIT.Feedback in
theorem solution {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (N : Channel α β) {n M : ℕ} (c : FeedbackCode α β n M) (hM : 0 < M) (ε : ℝ)
    (hε : c.errorProb N ≤ ε) :
    Real.logb 2 M ≤ n * channelMaxMutualInfo N + 1 + ε * Real.logb 2 M := by
  exact WildeQIT.FeedbackConverse.main N c hM ε hε
