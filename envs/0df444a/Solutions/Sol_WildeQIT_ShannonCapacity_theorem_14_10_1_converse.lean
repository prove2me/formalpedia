-- Prove2me | solution 1 for WildeQIT.ShannonCapacity.theorem_14_10_1_converse
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T16:01:24.708533+00:00
-- url     : https://prove2.me/submissions/cf22ee7c-68ce-430b-b564-ced6638b397d

import Mathlib
import Definitions.Def_WildeQIT_channelCode

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WildeQIT.ShannonConverse

open Finset WildeQIT

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

/-! ## The code-induced input distributions and the key inequality -/

section code
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The distribution of the `i`-th codeword letter under a uniformly random message. -/
noncomputable def pc {n M : ℕ} (hM : 0 < M) (c : ChannelCode α β n M) (i : Fin n) :
    FinDist α where
  prob a := ∑ m, if c.enc m i = a then (1 / M : ℝ) else 0
  nonneg a := Finset.sum_nonneg fun m _ => by split_ifs <;> positivity
  sum_eq_one := by
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq, hM']

lemma pc_prob {n M : ℕ} (hM : 0 < M) (c : ChannelCode α β n M) (i : Fin n) (a : α) :
    (pc hM c i).prob a = ∑ m, if c.enc m i = a then (1 / M : ℝ) else 0 := rfl

lemma pc_sum {n M : ℕ} (hM : 0 < M) (c : ChannelCode α β n M) (i : Fin n) (G : α → ℝ) :
    ∑ a, (pc hM c i).prob a * G a = ∑ m, (1 / M : ℝ) * G (c.enc m i) := by
  simp only [pc_prob, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [ite_mul]

lemma pc_pos {n M : ℕ} (hM : 0 < M) (c : ChannelCode α β n M) (i : Fin n) (m : Fin M) :
    0 < (pc hM c i).prob (c.enc m i) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : (0 : ℝ) < 1 / M := by positivity
  refine lt_of_lt_of_le h1 ?_
  rw [pc_prob]
  have := Finset.single_le_sum
    (f := fun m' => if c.enc m' i = c.enc m i then (1 / M : ℝ) else 0)
    (fun m' _ => by split_ifs <;> positivity) (Finset.mem_univ m)
  simpa using this

lemma Ip_pc (N : Channel α β) {n M : ℕ} (hM : 0 < M) (c : ChannelCode α β n M) (i : Fin n) :
    Ip N (pc hM c i) = ∑ m, (1 / M : ℝ) * ∑ b, (N (c.enc m i)).prob b *
      Real.logb 2 ((N (c.enc m i)).prob b / Q1 N (pc hM c i) b) := by
  unfold Ip idens
  have e : ∀ a, ∑ b, (pc hM c i).prob a * (N a).prob b *
        Real.logb 2 ((N a).prob b / Q1 N (pc hM c i) b)
      = (pc hM c i).prob a * ∑ b, (N a).prob b *
        Real.logb 2 ((N a).prob b / Q1 N (pc hM c i) b) := by
    intro a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp_rw [e]
  exact pc_sum hM c i _

/-- The product output distribution `∏ᵢ q_i(yᵢ)`. -/
noncomputable def Qn (N : Channel α β) {n M : ℕ} (hM : 0 < M) (c : ChannelCode α β n M)
    (y : Fin n → β) : ℝ :=
  ∏ i, Q1 N (pc hM c i) (y i)

lemma logsplit (N : Channel α β) {n M : ℕ} (hM : 0 < M) (c : ChannelCode α β n M) (m : Fin M)
    (y : Fin n → β) :
    N.seqProb (c.enc m) y * Real.logb 2 (N.seqProb (c.enc m) y / Qn N hM c y)
    = N.seqProb (c.enc m) y *
      ∑ i, Real.logb 2 ((N (c.enc m i)).prob (y i) / Q1 N (pc hM c i) (y i)) := by
  by_cases hW : N.seqProb (c.enc m) y = 0
  · simp [hW]
  · have hf : ∀ i, (N (c.enc m i)).prob (y i) ≠ 0 := by
      intro i hi
      apply hW
      unfold Channel.seqProb
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hq : ∀ i, Q1 N (pc hM c i) (y i) ≠ 0 := fun i =>
      (Q1_pos N _ (pc_pos hM c i m) (lt_of_le_of_ne ((N _).nonneg _) (Ne.symm (hf i)))).ne'
    congr 1
    unfold Channel.seqProb Qn
    rw [← Finset.prod_div_distrib]
    unfold Real.logb
    rw [Real.log_prod (fun i _ => div_ne_zero (hf i) (hq i)), Finset.sum_div]

lemma code_LHS (N : Channel α β) {n M : ℕ} (hM : 0 < M) (c : ChannelCode α β n M) (m : Fin M) :
    ∑ y, N.seqProb (c.enc m) y * Real.logb 2 (N.seqProb (c.enc m) y / Qn N hM c y)
    = ∑ i, ∑ b, (N (c.enc m i)).prob b *
        Real.logb 2 ((N (c.enc m i)).prob b / Q1 N (pc hM c i) b) := by
  simp_rw [logsplit N hM c m, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact marg1 n (fun j z => (N (c.enc m j)).prob z) (fun j => (N _).sum_eq_one)
    (fun z => Real.logb 2 ((N (c.enc m i)).prob z / Q1 N (pc hM c i) z)) i

/-- The decoding weight: `M/2` on the decoded message, `1/2` elsewhere. -/
noncomputable def gc {n M : ℕ} (c : ChannelCode α β n M) (m : Fin M) (y : Fin n → β) : ℝ :=
  1 / 2 + if c.dec y = m then ((M : ℝ) - 1) / 2 else 0

lemma logb_gc {n M : ℕ} (hM : 0 < M) (c : ChannelCode α β n M) (m : Fin M) (y : Fin n → β) :
    Real.logb 2 (gc c m y) = -1 + if c.dec y = m then Real.logb 2 M else 0 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold gc
  split_ifs
  · rw [show (1 / 2 + ((M : ℝ) - 1) / 2) = (M : ℝ) / 2 by ring,
      Real.logb_div hM' two_ne_zero, Real.logb_self_eq_one one_lt_two]
    ring
  · rw [add_zero, one_div, Real.logb_inv, Real.logb_self_eq_one one_lt_two]
    ring

/-- **Key inequality** (Gibbs + memorylessness): `(1-ε) log₂ M - 1 ≤ ∑ᵢ I(Xᵢ;Yᵢ)`. -/
lemma key (N : Channel α β) {n M : ℕ} (hM : 0 < M) (c : ChannelCode α β n M) {ε : ℝ}
    (herr : ∀ m, c.errorProb N m ≤ ε) :
    (1 - ε) * Real.logb 2 M - 1 ≤ ∑ i, Ip N (pc hM c i) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hW0 : ∀ m y, 0 ≤ N.seqProb (c.enc m) y := fun m y =>
    Finset.prod_nonneg fun i _ => (N _).nonneg _
  have hW1 : ∀ m, ∑ y, N.seqProb (c.enc m) y = 1 := fun m =>
    (sum_prod_eq n (fun i z => (N (c.enc m i)).prob z)).trans (by simp [(N _).sum_eq_one])
  have hQ0 : ∀ y, 0 ≤ Qn N hM c y := fun y =>
    Finset.prod_nonneg fun i _ => Q1_nonneg N _ _
  have hQ1 : ∑ y, Qn N hM c y = 1 :=
    (sum_prod_eq n (fun i z => Q1 N (pc hM c i) z)).trans (by simp [Q1_sum])
  have hQpos : ∀ m y, 0 < N.seqProb (c.enc m) y → 0 < Qn N hM c y := by
    intro m y hW
    unfold Qn
    refine Finset.prod_pos fun i _ => Q1_pos N _ (pc_pos hM c i m) ?_
    refine lt_of_le_of_ne ((N _).nonneg _) (fun h => hW.ne' ?_)
    unfold Channel.seqProb
    exact Finset.prod_eq_zero (Finset.mem_univ i) h.symm
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
  -- the Gibbs inequality on `Fin M × (Fin n → β)`
  have hG := gibbs (fun z : Fin M × (Fin n → β) => N.seqProb (c.enc z.1) z.2 / M)
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
  -- the mutual-information part
  have hA : ∑ z : Fin M × (Fin n → β), N.seqProb (c.enc z.1) z.2 / M *
      Real.logb 2 (N.seqProb (c.enc z.1) z.2 / Qn N hM c z.2) = ∑ i, Ip N (pc hM c i) := by
    have h1 : ∀ m, ∑ y, N.seqProb (c.enc m) y / M *
        Real.logb 2 (N.seqProb (c.enc m) y / Qn N hM c y)
        = ∑ i, (1 / M : ℝ) * ∑ b, (N (c.enc m i)).prob b *
          Real.logb 2 ((N (c.enc m i)).prob b / Q1 N (pc hM c i) b) := by
      intro m
      rw [← Finset.mul_sum, ← code_LHS N hM c m, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    simp only [Fintype.sum_prod_type, h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (Ip_pc N hM c i).symm
  -- the decoding part
  have hcorr : ∀ m, ∑ y, (if c.dec y = m then N.seqProb (c.enc m) y else 0)
      = 1 - c.errorProb N m := by
    intro m
    rw [← hW1 m, ChannelCode.errorProb, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
  have hlogM : 0 ≤ Real.logb 2 M := Real.logb_nonneg one_lt_two hM1
  have hB : (1 - ε) * Real.logb 2 M - 1 ≤ ∑ z : Fin M × (Fin n → β),
      N.seqProb (c.enc z.1) z.2 / M * Real.logb 2 (gc c z.1 z.2) := by
    have e : ∀ z : Fin M × (Fin n → β), N.seqProb (c.enc z.1) z.2 / M * Real.logb 2 (gc c z.1 z.2)
        = -(N.seqProb (c.enc z.1) z.2 / M) + Real.logb 2 M *
          ((1 / M : ℝ) * if c.dec z.2 = z.1 then N.seqProb (c.enc z.1) z.2 else 0) := by
      intro z
      rw [logb_gc hM]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun z _ => e z, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum]
    have hP1 : ∑ z : Fin M × (Fin n → β), N.seqProb (c.enc z.1) z.2 / M = 1 := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.sum_div, hW1]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hS : 1 - ε ≤ ∑ z : Fin M × (Fin n → β),
        (1 / M : ℝ) * (if c.dec z.2 = z.1 then N.seqProb (c.enc z.1) z.2 else 0) := by
      rw [Fintype.sum_prod_type]
      simp only []
      simp_rw [← Finset.mul_sum, hcorr]
      calc 1 - ε = ∑ _m : Fin M, (1 / M : ℝ) * (1 - ε) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
        _ ≤ ∑ m : Fin M, (1 / M : ℝ) * (1 - c.errorProb N m) :=
            Finset.sum_le_sum fun m _ => by
              have := herr m
              have : (0 : ℝ) ≤ 1 / M := by positivity
              nlinarith
        _ = 1 / M * ∑ m : Fin M, (1 - c.errorProb N m) := by rw [Finset.mul_sum]
    rw [hP1]
    nlinarith [mul_le_mul_of_nonneg_left hS hlogM]
  linarith

end code

theorem main {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (N : Channel α β) (R : ℝ) (hR : IsAchievableChannelRate N R) :
    R ≤ channelMaxMutualInfo N := by
  classical
  by_contra hlt
  push_neg at hlt
  set C := channelMaxMutualInfo N with hC
  have hg : 0 < R - C := by linarith
  set δ := (R - C) / 4 with hδ
  set A := |R - δ| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  set ε := min (1 / 2 : ℝ) ((R - C) / (4 * (A + 1))) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hεA : ε * A ≤ (R - C) / 4 := by
    have h1 : ε ≤ (R - C) / (4 * (A + 1)) := min_le_right _ _
    have h2 : ε * (A + 1) ≤ (R - C) / 4 := by
      calc ε * (A + 1) ≤ (R - C) / (4 * (A + 1)) * (A + 1) := by gcongr
        _ = (R - C) / 4 := by field_simp
    nlinarith
  obtain ⟨N₀, hN₀⟩ := hR ε hε0 hε1 δ (by positivity)
  set n := max N₀ (⌈4 / (R - C)⌉₊ + 1) with hn
  obtain ⟨M, hM, c, herr⟩ := hN₀ n (le_max_left _ _)
  have hn1 : 4 / (R - C) < n := by
    have h0 : (⌈4 / (R - C)⌉₊ + 1 : ℕ) ≤ n := le_max_right _ _
    have h2 : 4 / (R - C) ≤ ⌈4 / (R - C)⌉₊ := Nat.le_ceil _
    have h3 : ((⌈4 / (R - C)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h0
    push_cast at h3
    linarith
  have hng : 4 < (n : ℝ) * (R - C) := by
    rw [div_lt_iff₀ hg] at hn1
    linarith
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (Real.rpow_pos_of_pos two_pos _) hM
  have hM0 : 0 < M := by exact_mod_cast hMpos
  have hlog : (n : ℝ) * (R - δ) ≤ Real.logb 2 M :=
    (Real.le_logb_iff_rpow_le one_lt_two hMpos).2 hM
  have hkey := key N hM0 c herr
  have hsum : ∑ i, Ip N (pc hM0 c i) ≤ n * C := by
    calc ∑ i, Ip N (pc hM0 c i) ≤ ∑ _i : Fin n, C := Finset.sum_le_sum fun i _ => by
          rw [mi_eq, hC]
          exact le_csSup (bdd N) ⟨_, rfl⟩
      _ = n * C := by simp
  have h1 : (1 - ε) * ((n : ℝ) * (R - δ)) ≤ (1 - ε) * Real.logb 2 M :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  have h2 : (R - δ) - ε * A ≤ (1 - ε) * (R - δ) := by
    have : ε * (R - δ) ≤ ε * A := mul_le_mul_of_nonneg_left (le_abs_self _) hε0.le
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h3 : (n : ℝ) * ((R - δ) - ε * A) ≤ (1 - ε) * ((n : ℝ) * (R - δ)) := by
    calc (n : ℝ) * ((R - δ) - ε * A) ≤ n * ((1 - ε) * (R - δ)) :=
          mul_le_mul_of_nonneg_left h2 hn0
      _ = (1 - ε) * ((n : ℝ) * (R - δ)) := by ring
  have h4 : (n : ℝ) * (C + (R - C) / 2) ≤ n * ((R - δ) - ε * A) :=
    mul_le_mul_of_nonneg_left (by rw [hδ]; linarith) hn0
  have h5 : (n : ℝ) * (C + (R - C) / 2) = n * C + n * (R - C) / 2 := by ring
  linarith

end WildeQIT.ShannonConverse

open WildeQIT in
theorem solution {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (N : Channel α β) (R : ℝ) (hR : IsAchievableChannelRate N R) :
    R ≤ channelMaxMutualInfo N := by
  exact WildeQIT.ShannonConverse.main N R hR
