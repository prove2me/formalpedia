-- Prove2me | solution 1 for WildeQIT.ShannonCapacity.theorem_14_10_1_direct
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T15:48:25.406032+00:00
-- url     : https://prove2.me/submissions/d081cdaf-bbf1-4215-97c4-d9a8e968d1b1

import Mathlib
import Definitions.Def_WildeQIT_channelCode

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WildeQIT.ShannonDirect

open Finset WildeQIT

/-! ## Feinstein's maximal-code lemma (finite, general alphabets) -/

section Feinstein

variable {A B : Type} [Fintype A] [Fintype B]

/-- A partial Feinstein code: codewords, a partial decoder whose decoding sets lie in the
"good" sets `{b : γ Q b < W a b}` and have conditional probability at least `1 - ε`. -/
structure PCode (W : A → B → ℝ) (Q : B → ℝ) (γ ε : ℝ) where
  M : ℕ
  enc : Fin M → A
  dec : B → Option (Fin M)
  good : ∀ b m, dec b = some m → γ * Q b < W (enc m) b
  big : ∀ m, 1 - ε ≤ ∑ b, if dec b = some m then W (enc m) b else 0

variable {W : A → B → ℝ} {Q : B → ℝ} {γ ε : ℝ}

/-- Number of decoded outputs. -/
noncomputable def PCode.size (c : PCode W Q γ ε) : ℕ := (univ.filter fun b => c.dec b ≠ none).card

def PCode.empty : PCode W Q γ ε where
  M := 0
  enc := Fin.elim0
  dec := fun _ => none
  good := fun _ _ h => by simp at h
  big := fun m => m.elim0

lemma PCode.size_le (c : PCode W Q γ ε) : c.size ≤ Fintype.card B :=
  card_filter_le _ _

/-- The extended decoder. -/
noncomputable def decExt (c : PCode W Q γ ε) (x : A) (b : B) : Option (Fin (c.M + 1)) :=
  (c.dec b).elim (if γ * Q b < W x b then some (Fin.last c.M) else none)
    (fun m => some m.castSucc)

lemma decExt_castSucc (c : PCode W Q γ ε) (x : A) (b : B) (m : Fin c.M) :
    decExt c x b = some m.castSucc ↔ c.dec b = some m := by
  cases h : c.dec b with
  | none =>
    simp only [decExt, h, Option.elim_none]
    split_ifs <;> simp [(Fin.castSucc_lt_last m).ne']
  | some m' =>
    simp [decExt, h]

lemma decExt_last (c : PCode W Q γ ε) (x : A) (b : B) :
    decExt c x b = some (Fin.last c.M) ↔ (c.dec b = none ∧ γ * Q b < W x b) := by
  cases h : c.dec b with
  | none =>
    simp only [decExt, h, Option.elim_none, true_and]
    split_ifs with h1 <;> simp [h1]
  | some m' =>
    simp [decExt, h, (Fin.castSucc_lt_last m').ne]

lemma decExt_none (c : PCode W Q γ ε) (x : A) (b : B) :
    decExt c x b = none ↔ (c.dec b = none ∧ ¬ γ * Q b < W x b) := by
  cases h : c.dec b with
  | none =>
    simp only [decExt, h, Option.elim_none, true_and]
    split_ifs with h1 <;> simp [h1]
  | some m' =>
    simp [decExt, h]

noncomputable def PCode.ext (c : PCode W Q γ ε) (x : A)
    (hx : 1 - ε ≤ ∑ b, if c.dec b = none ∧ γ * Q b < W x b then W x b else 0) :
    PCode W Q γ ε where
  M := c.M + 1
  enc := Fin.snoc (α := fun _ => A) c.enc x
  dec := decExt c x
  good := by
    intro b m hm
    induction m using Fin.lastCases with
    | last =>
      rw [decExt_last] at hm
      simpa using hm.2
    | cast m =>
      rw [decExt_castSucc] at hm
      simpa using c.good b m hm
  big := by
    intro m
    induction m using Fin.lastCases with
    | last =>
      refine hx.trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [decExt_last, Fin.snoc_last]
    | cast m =>
      refine (c.big m).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [decExt_castSucc, Fin.snoc_castSucc]

lemma PCode.size_lt_ext (hε : ε < 1) (c : PCode W Q γ ε) (x : A)
    (hx : 1 - ε ≤ ∑ b, if c.dec b = none ∧ γ * Q b < W x b then W x b else 0) :
    c.size < (c.ext x hx).size := by
  unfold PCode.size
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · have hne : (∑ b, if c.dec b = none ∧ γ * Q b < W x b then W x b else 0) ≠ 0 := by
      intro h0; rw [h0] at hx; linarith
    obtain ⟨b, _, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hb' : c.dec b = none ∧ γ * Q b < W x b := by
      by_contra hc; rw [if_neg hc] at hb; exact hb rfl
    refine ⟨b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show decExt c x b ≠ none
      rw [(decExt_last c x b).mpr hb']; simp
    · simp [hb'.1]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    show decExt c x b ≠ none
    rw [Ne, decExt_none]; tauto

lemma exists_maximal (hε : ε < 1) :
    ∃ c : PCode W Q γ ε, ∀ x,
      (∑ b, if c.dec b = none ∧ γ * Q b < W x b then W x b else 0) < 1 - ε := by
  by_contra hcon
  push Not at hcon
  have key : ∀ k : ℕ, ∃ c : PCode W Q γ ε, k ≤ c.size := by
    intro k
    induction k with
    | zero => exact ⟨PCode.empty, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨x, hx⟩ := hcon c
      exact ⟨c.ext x hx, lt_of_le_of_lt hc (c.size_lt_ext hε x hx)⟩
  obtain ⟨c, hc⟩ := key (Fintype.card B + 1)
  have := c.size_le
  omega

lemma maximal_bound (hW0 : ∀ a b, 0 ≤ W a b) (hW1 : ∀ a, ∑ b, W a b = 1)
    (P : A → ℝ) (hP0 : ∀ a, 0 ≤ P a) (hP1 : ∑ a, P a = 1)
    (hQ : ∀ b, ∑ a, P a * W a b ≤ Q b) (hγ : 0 < γ) (c : PCode W Q γ ε)
    (hmax : ∀ x, (∑ b, if c.dec b = none ∧ γ * Q b < W x b then W x b else 0) < 1 - ε) :
    γ * (ε - ∑ a, P a * ∑ b, if W a b ≤ γ * Q b then W a b else 0) ≤ c.M := by
  set Pbad := ∑ a, P a * ∑ b, if W a b ≤ γ * Q b then W a b else 0
  have step1 : ∀ a, 1 ≤ (∑ b, if W a b ≤ γ * Q b then W a b else 0) + (1 - ε)
      + ∑ b, (if c.dec b = none then 0 else W a b) := by
    intro a
    have hpt : ∀ b, W a b ≤ (if W a b ≤ γ * Q b then W a b else 0)
        + (if c.dec b = none ∧ γ * Q b < W a b then W a b else 0)
        + (if c.dec b = none then 0 else W a b) := by
      intro b
      have := hW0 a b
      by_cases h1 : W a b ≤ γ * Q b
      · rw [if_pos h1]; split_ifs <;> linarith
      · rw [if_neg h1]
        have h1' : γ * Q b < W a b := lt_of_not_ge h1
        by_cases h2 : c.dec b = none
        · rw [if_pos ⟨h2, h1'⟩, if_pos h2]; linarith
        · rw [if_neg (fun h => h2 h.1), if_neg h2]; linarith
    have hs := Finset.sum_le_sum fun b (_ : b ∈ univ) => hpt b
    rw [hW1 a, Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
    linarith [hmax a]
  have step2 : 1 ≤ Pbad + (1 - ε) + ∑ b, (if c.dec b = none then 0 else Q b) := by
    have h1 : ∑ a, P a * 1 ≤ ∑ a, P a * ((∑ b, if W a b ≤ γ * Q b then W a b else 0) + (1 - ε)
        + ∑ b, (if c.dec b = none then 0 else W a b)) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (step1 a) (hP0 a)
    have h2 : ∑ a, P a * ∑ b, (if c.dec b = none then 0 else W a b)
        ≤ ∑ b, (if c.dec b = none then 0 else Q b) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun b _ => ?_
      split_ifs
      · simp
      · exact hQ b
    simp only [mul_one, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hP1, one_mul] at h1
    linarith
  have step3 : γ * ∑ b, (if c.dec b = none then 0 else Q b) ≤ c.M := by
    have hb : ∀ b, γ * (if c.dec b = none then 0 else Q b)
        ≤ ∑ m, if c.dec b = some m then W (c.enc m) b else 0 := by
      intro b
      cases h : c.dec b with
      | none =>
        simp only [if_true, mul_zero, reduceCtorEq, if_false, Finset.sum_const_zero, le_refl]
      | some m0 =>
        simp only [reduceCtorEq, if_false, Option.some.injEq]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
        exact (c.good b m0 h).le
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun b _ => hb b).trans ?_
    rw [Finset.sum_comm]
    have : ∀ m : Fin c.M, (∑ b, if c.dec b = some m then W (c.enc m) b else 0) ≤ 1 := by
      intro m
      rw [← hW1 (c.enc m)]
      refine Finset.sum_le_sum fun b _ => ?_
      split_ifs
      · exact le_refl _
      · exact hW0 _ _
    refine (Finset.sum_le_sum fun m _ => this m).trans ?_
    simp
  nlinarith

/-- **Feinstein's lemma** (maximal-code form). -/
theorem feinstein (hW0 : ∀ a b, 0 ≤ W a b) (hW1 : ∀ a, ∑ b, W a b = 1)
    (P : A → ℝ) (hP0 : ∀ a, 0 ≤ P a) (hP1 : ∑ a, P a = 1)
    (hQ : ∀ b, ∑ a, P a * W a b ≤ Q b) (hγ : 0 < γ) (hε : ε < 1) :
    ∃ (M : ℕ) (enc : Fin M → A) (dec : B → Option (Fin M)),
      (∀ m, 1 - ε ≤ ∑ b, if dec b = some m then W (enc m) b else 0) ∧
      γ * (ε - ∑ a, P a * ∑ b, if W a b ≤ γ * Q b then W a b else 0) ≤ M := by
  obtain ⟨c, hc⟩ := exists_maximal (W := W) (Q := Q) (γ := γ) hε
  exact ⟨c.M, c.enc, c.dec, c.big, maximal_bound hW0 hW1 P hP0 hP1 hQ hγ c hc⟩

end Feinstein


/-! ## i.i.d. sums and Chebyshev -/

section LLN

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

lemma iid_one (q : FinDist Z) (n : ℕ) : ∑ x : Fin n → Z, ∏ i, q.prob (x i) = 1 :=
  (sum_prod_eq n (fun _ z => q.prob z)).trans (by simp [q.sum_eq_one])

lemma iid_mean (p : FinDist Z) (h : Z → ℝ) (hm : ∑ a, p.prob a * h a = 0) (n : ℕ) :
    ∑ x : Fin n → Z, (∏ i, p.prob (x i)) * ∑ i, h (x i) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have h1 : ∀ a, ∑ x : Fin n → Z, (p.prob a * ∏ i, p.prob (x i)) * (h a + ∑ i, h (x i))
        = p.prob a * h a := by
      intro a
      calc _ = p.prob a * h a * ∑ x : Fin n → Z, ∏ i, p.prob (x i)
              + p.prob a * ∑ x : Fin n → Z, (∏ i, p.prob (x i)) * ∑ i, h (x i) := by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun x _ => by ring
        _ = _ := by rw [iid_one, ih]; ring
    rw [Finset.sum_congr rfl fun a _ => h1 a, hm]

lemma iid_var (p : FinDist Z) (h : Z → ℝ) (hm : ∑ a, p.prob a * h a = 0) (n : ℕ) :
    ∑ x : Fin n → Z, (∏ i, p.prob (x i)) * (∑ i, h (x i)) ^ 2
      = n * ∑ a, p.prob a * h a ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have h1 : ∀ a, ∑ x : Fin n → Z, (p.prob a * ∏ i, p.prob (x i)) * (h a + ∑ i, h (x i)) ^ 2
        = p.prob a * h a ^ 2 + p.prob a * (n * ∑ a, p.prob a * h a ^ 2) := by
      intro a
      calc _ = p.prob a * h a ^ 2 * ∑ x : Fin n → Z, ∏ i, p.prob (x i)
              + 2 * p.prob a * h a * ∑ x : Fin n → Z, (∏ i, p.prob (x i)) * ∑ i, h (x i)
              + p.prob a * ∑ x : Fin n → Z, (∏ i, p.prob (x i)) * (∑ i, h (x i)) ^ 2 := by
                rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
                  ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun x _ => by ring
        _ = _ := by rw [iid_one, iid_mean p h hm, ih]; ring
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_add_distrib, ← Finset.sum_mul,
      p.sum_eq_one]
    push_cast
    ring

lemma cheb (q : FinDist Z) (h : Z → ℝ) (hm : ∑ a, q.prob a * h a = 0) (n : ℕ) (t : ℝ)
    (ht : 0 < t) :
    ∑ x : Fin n → Z, (if t ≤ |∑ i, h (x i)| then ∏ i, q.prob (x i) else 0)
      ≤ (n * ∑ a, q.prob a * h a ^ 2) / t ^ 2 := by
  rw [le_div_iff₀ (by positivity), ← iid_var q h hm n, Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  have hp : 0 ≤ ∏ i, q.prob (x i) := Finset.prod_nonneg fun i _ => q.nonneg (x i)
  split_ifs with h2
  · apply mul_le_mul_of_nonneg_left _ hp
    rw [← sq_abs (∑ i, h (x i))]
    exact pow_le_pow_left₀ ht.le h2 2
  · rw [zero_mul]; exact mul_nonneg hp (sq_nonneg _)

end LLN

/-! ## The n-letter channel and the information density -/

section Chan

variable {α β : Type} [Fintype α] [Fintype β]

noncomputable def Q1 (N : Channel α β) (p : FinDist α) (y : β) : ℝ := ∑ x, p.prob x * (N x).prob y

noncomputable def idens (N : Channel α β) (p : FinDist α) (x : α) (y : β) : ℝ :=
  Real.logb 2 ((N x).prob y / Q1 N p y)

noncomputable def Ip (N : Channel α β) (p : FinDist α) : ℝ :=
  ∑ x, ∑ y, p.prob x * (N x).prob y * idens N p x y

noncomputable def hc (N : Channel α β) (p : FinDist α) (z : α × β) : ℝ := idens N p z.1 z.2 - Ip N p

lemma hc_mean (N : Channel α β) (p : FinDist α) : ∑ z, (N.joint p).prob z * hc N p z = 0 := by
  have e : ∀ x y, p.prob x * (N x).prob y * hc N p (x, y)
      = p.prob x * (N x).prob y * idens N p x y - p.prob x * (N x).prob y * Ip N p :=
    fun x y => by simp only [hc]; ring
  have hI : ∑ x, ∑ y, p.prob x * (N x).prob y * Ip N p = Ip N p := by
    have : ∀ x, ∑ y, p.prob x * (N x).prob y * Ip N p = p.prob x * Ip N p := fun x => by
      rw [← Finset.sum_mul, ← Finset.mul_sum, (N x).sum_eq_one, mul_one]
    rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_mul, p.sum_eq_one, one_mul]
  rw [Fintype.sum_prod_type]
  simp only [Channel.joint_prob]
  simp only [e, Finset.sum_sub_distrib, hI]
  unfold Ip
  exact sub_self _

lemma Q1_pos (N : Channel α β) (p : FinDist α) {x : α} {y : β} (hp : 0 < p.prob x)
    (hw : 0 < (N x).prob y) : 0 < Q1 N p y :=
  lt_of_lt_of_le (mul_pos hp hw)
    (Finset.single_le_sum (f := fun a => p.prob a * (N a).prob y)
      (fun a _ => mul_nonneg (p.nonneg a) ((N a).nonneg y)) (Finset.mem_univ x))

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

lemma seq_nonneg (N : Channel α β) {n : ℕ} (x : Fin n → α) (y : Fin n → β) :
    0 ≤ N.seqProb x y :=
  Finset.prod_nonneg fun i _ => (N (x i)).nonneg (y i)

lemma seq_one (N : Channel α β) {n : ℕ} (x : Fin n → α) : ∑ y, N.seqProb x y = 1 :=
  (sum_prod_eq n (fun i z => (N (x i)).prob z)).trans (by simp [(N _).sum_eq_one])

lemma hQn (N : Channel α β) (p : FinDist α) {n : ℕ} (y : Fin n → β) :
    ∑ x : Fin n → α, (∏ i, p.prob (x i)) * N.seqProb x y = ∏ i, Q1 N p (y i) := by
  have := sum_prod_eq n (fun i a => p.prob a * (N a).prob (y i))
  simp only [Q1]
  rw [← this]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Channel.seqProb, ← Finset.prod_mul_distrib]

def pairEquiv (n : ℕ) : (Fin n → α × β) ≃ (Fin n → α) × (Fin n → β) where
  toFun z := (fun i => (z i).1, fun i => (z i).2)
  invFun w := fun i => (w.1 i, w.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

lemma pt (N : Channel α β) (p : FinDist α) {n : ℕ} (δ : ℝ) (x : Fin n → α) (y : Fin n → β) :
    (if N.seqProb x y ≤ (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ / 2)) * ∏ i, Q1 N p (y i)
      then (∏ i, p.prob (x i)) * N.seqProb x y else 0)
    ≤ if (n:ℝ) * δ / 2 ≤ |∑ i, hc N p (x i, y i)|
      then (∏ i, p.prob (x i)) * N.seqProb x y else 0 := by
  have hPW : 0 ≤ (∏ i, p.prob (x i)) * N.seqProb x y :=
    mul_nonneg (Finset.prod_nonneg fun i _ => p.nonneg _) (seq_nonneg N x y)
  split_ifs with h1 h2 h2
  · exact le_refl _
  · by_contra hpos
    apply h2
    have hne : (∏ i, p.prob (x i)) * N.seqProb x y ≠ 0 := by
      intro h0; rw [h0] at hpos; exact hpos (le_refl _)
    rw [mul_ne_zero_iff, Finset.prod_ne_zero_iff, Channel.seqProb, Finset.prod_ne_zero_iff] at hne
    have hp : ∀ i, 0 < p.prob (x i) := fun i =>
      lt_of_le_of_ne (p.nonneg _) (hne.1 i (Finset.mem_univ _)).symm
    have hw : ∀ i, 0 < (N (x i)).prob (y i) := fun i =>
      lt_of_le_of_ne ((N (x i)).nonneg _) (hne.2 i (Finset.mem_univ _)).symm
    have hq : ∀ i, 0 < Q1 N p (y i) := fun i => Q1_pos N p (hp i) (hw i)
    have hWpos : 0 < N.seqProb x y := Finset.prod_pos fun i _ => hw i
    have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hWpos h1
    rw [Real.logb_mul (Real.rpow_pos_of_pos two_pos _).ne'
        (Finset.prod_pos fun i _ => hq i).ne', Real.logb_rpow two_pos (by norm_num),
      Channel.seqProb, Real.logb_prod _ _ (fun i _ => (hw i).ne'),
      Real.logb_prod _ _ (fun i _ => (hq i).ne')] at hlog
    have hsum : ∑ i, hc N p (x i, y i) = ∑ i, Real.logb 2 ((N (x i)).prob (y i))
        - ∑ i, Real.logb 2 (Q1 N p (y i)) - n * Ip N p := by
      simp only [hc, idens, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.sum_congr rfl fun i _ => Real.logb_div (hw i).ne' (hq i).ne',
        Finset.sum_sub_distrib]
    rw [hsum]
    exact le_abs.mpr (Or.inr (by linarith))
  · exact hPW
  · exact le_refl _

lemma pbad_le (N : Channel α β) (p : FinDist α) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hn : 0 < n) :
    (∑ x : Fin n → α, (∏ i, p.prob (x i)) * ∑ y : Fin n → β,
        if N.seqProb x y ≤ (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ / 2)) * ∏ i, Q1 N p (y i)
        then N.seqProb x y else 0)
      ≤ (n * ∑ z, (N.joint p).prob z * hc N p z ^ 2) / ((n:ℝ) * δ / 2) ^ 2 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  refine le_trans ?_ (cheb (N.joint p) (hc N p) (hc_mean N p) n _ (by positivity))
  have hR : (∑ z : Fin n → α × β, if (n:ℝ) * δ / 2 ≤ |∑ i, hc N p (z i)|
        then ∏ i, (N.joint p).prob (z i) else 0)
      = ∑ x : Fin n → α, ∑ y : Fin n → β, if (n:ℝ) * δ / 2 ≤ |∑ i, hc N p (x i, y i)|
        then (∏ i, p.prob (x i)) * N.seqProb x y else 0 := by
    rw [Fintype.sum_equiv (pairEquiv n) _ (fun w : (Fin n → α) × (Fin n → β) =>
      if (n:ℝ) * δ / 2 ≤ |∑ i, hc N p (w.1 i, w.2 i)|
        then (∏ i, p.prob (w.1 i)) * N.seqProb w.1 w.2 else 0) ?_, Fintype.sum_prod_type]
    intro z
    simp only [pairEquiv, Equiv.coe_fn_mk, Prod.mk.eta, Channel.seqProb,
      ← Finset.prod_mul_distrib]
    rfl
  rw [hR]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  refine le_trans (le_of_eq ?_) (pt N p δ x y)
  split_ifs <;> simp

end Chan


/-! ## Achievability of `I(X;Y)` for every input distribution, and the theorem -/

theorem perp {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (N : Channel α β)
    (p : FinDist α) : IsAchievableChannelRate N (Ip N p) := by
  intro ε hε0 hε1 δ hδ
  have hV0 : 0 ≤ ∑ z, (N.joint p).prob z * hc N p z ^ 2 :=
    Finset.sum_nonneg fun z _ => mul_nonneg ((N.joint p).nonneg z) (sq_nonneg _)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨⌈8 * (∑ z, (N.joint p).prob z * hc N p z ^ 2) / (ε * δ ^ 2)⌉₊
    + ⌈4 / (ε * δ * Real.log 2)⌉₊ + 1, fun n hn => ?_⟩
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have c1 : ⌈8 * (∑ z, (N.joint p).prob z * hc N p z ^ 2) / (ε * δ ^ 2)⌉₊ ≤ n := by omega
  have c2 : ⌈4 / (ε * δ * Real.log 2)⌉₊ ≤ n := by omega
  have hn1 : 8 * (∑ z, (N.joint p).prob z * hc N p z ^ 2) / (ε * δ ^ 2) ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast c1)
  have hn2 : 4 / (ε * δ * Real.log 2) ≤ (n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast c2)
  have hγ0 : (0:ℝ) < (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ / 2)) := Real.rpow_pos_of_pos two_pos _
  obtain ⟨M, enc, dec, hbig, hM⟩ := feinstein (A := Fin n → α) (B := Fin n → β)
    (W := fun x y => N.seqProb x y) (Q := fun y => ∏ i, Q1 N p (y i))
    (γ := (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ / 2))) (ε := ε)
    (fun x y => seq_nonneg N x y) (fun x => seq_one N x) (fun x => ∏ i, p.prob (x i))
    (fun x => Finset.prod_nonneg fun i _ => p.nonneg _) (iid_one p n)
    (fun y => (hQn N p y).le) hγ0 hε1
  have hPb := pbad_le N p n δ hδ hnpos
  have hPb2 : (n * ∑ z, (N.joint p).prob z * hc N p z ^ 2) / ((n:ℝ) * δ / 2) ^ 2 ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hn1
    nlinarith [mul_le_mul_of_nonneg_left hn1 hnR.le]
  have hexp : 2 / ε ≤ (2:ℝ) ^ ((n:ℝ) * (δ / 2)) := by
    rw [Real.rpow_def_of_pos two_pos]
    refine le_trans ?_ (Real.add_one_le_exp _)
    rw [div_le_iff₀ (by positivity)] at hn2
    rw [div_le_iff₀ hε0]
    nlinarith
  have hkey : (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ)) ≤ M := by
    have hsplit : (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ / 2))
        = (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ)) * (2:ℝ) ^ ((n:ℝ) * (δ / 2)) := by
      rw [← Real.rpow_add two_pos]; ring_nf
    have hA : 0 < (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ)) := Real.rpow_pos_of_pos two_pos _
    have h1 : 1 ≤ (2:ℝ) ^ ((n:ℝ) * (δ / 2)) * (ε / 2) := by
      have h2 := (div_le_iff₀ hε0).mp hexp
      nlinarith
    calc (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ))
        ≤ (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ)) * ((2:ℝ) ^ ((n:ℝ) * (δ / 2)) * (ε / 2)) := by
          nlinarith
      _ = (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ / 2)) * (ε / 2) := by rw [hsplit]; ring
      _ ≤ (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ / 2)) * (ε - ∑ x : Fin n → α, (∏ i, p.prob (x i)) *
            ∑ y : Fin n → β, if N.seqProb x y ≤ (2:ℝ) ^ ((n:ℝ) * (Ip N p - δ / 2))
              * ∏ i, Q1 N p (y i) then N.seqProb x y else 0) :=
          mul_le_mul_of_nonneg_left (by linarith) hγ0.le
      _ ≤ M := hM
  have hMpos : 0 < M := by
    have : (0:ℝ) < M := lt_of_lt_of_le (Real.rpow_pos_of_pos two_pos _) hkey
    exact_mod_cast this
  refine ⟨M, hkey, ⟨enc, fun y => (dec y).getD ⟨0, hMpos⟩⟩, fun m => ?_⟩
  show (∑ y, if (dec y).getD ⟨0, hMpos⟩ = m then 0 else N.seqProb (enc m) y) ≤ ε
  have hle : ∀ y, (if (dec y).getD ⟨0, hMpos⟩ = m then 0 else N.seqProb (enc m) y)
      ≤ N.seqProb (enc m) y - (if dec y = some m then N.seqProb (enc m) y else 0) := by
    intro y
    have h0 := seq_nonneg N (enc m) y
    by_cases h : dec y = some m
    · simp [h]
    · rw [if_neg h]; split_ifs <;> linarith
  calc _ ≤ ∑ y, (N.seqProb (enc m) y - (if dec y = some m then N.seqProb (enc m) y else 0)) :=
        Finset.sum_le_sum fun y _ => hle y
    _ = 1 - ∑ y, (if dec y = some m then N.seqProb (enc m) y else 0) := by
        rw [Finset.sum_sub_distrib, seq_one]
    _ ≤ ε := by linarith [hbig m]

theorem main {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (N : Channel α β) : IsAchievableChannelRate N (channelMaxMutualInfo N) := by
  intro ε hε0 hε1 δ hδ
  by_cases hS : BddAbove {I : ℝ | ∃ p : FinDist α, I = mutualInfo (N.joint p)} ∧
      ({I : ℝ | ∃ p : FinDist α, I = mutualInfo (N.joint p)}).Nonempty
  · obtain ⟨I, ⟨p, rfl⟩, hI⟩ := exists_lt_of_lt_csSup hS.2
      (show channelMaxMutualInfo N - δ / 2 < channelMaxMutualInfo N by linarith)
    obtain ⟨N0, hN0⟩ := perp N p ε hε0 hε1 (δ / 2) (by linarith)
    refine ⟨N0, fun n hn => ?_⟩
    obtain ⟨M, hM, c, hc⟩ := hN0 n hn
    refine ⟨M, le_trans ?_ hM, c, hc⟩
    rw [← mi_eq] at hI
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    linarith
  · have h0 : channelMaxMutualInfo N = 0 := by
      unfold channelMaxMutualInfo
      rcases not_and_or.mp hS with h | h
      · exact Real.sSup_of_not_bddAbove h
      · rw [Set.not_nonempty_iff_eq_empty.mp h]; exact Real.sSup_empty
    rw [h0]
    refine ⟨0, fun n _ => ⟨1, ?_, ⟨fun _ _ => Classical.arbitrary α, fun _ => 0⟩, fun m => ?_⟩⟩
    · rw [Nat.cast_one]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
    · have hm : m = 0 := Subsingleton.elim _ _
      subst hm
      refine le_trans (le_of_eq ?_) hε0.le
      simp [ChannelCode.errorProb]

end WildeQIT.ShannonDirect

open WildeQIT in
theorem solution {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (N : Channel α β) :
    IsAchievableChannelRate N (channelMaxMutualInfo N) := by
  exact WildeQIT.ShannonDirect.main N
