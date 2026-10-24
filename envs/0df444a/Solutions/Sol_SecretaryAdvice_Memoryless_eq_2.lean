-- Prove2me | solution 1 for SecretaryAdvice.Memoryless.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T01:01:41.56199+00:00
-- url     : https://prove2.me/submissions/48d6031e-73c2-4389-87fb-433e4b01165c

import Mathlib
import Definitions.Def_SecretaryAdvice_Memoryless_Setting
import Definitions.Def_SecretaryAdvice_Memoryless_LP

open SecretaryAdvice.Memoryless

namespace SMA

open Classical

set_option linter.unusedSectionVars false

variable {n : ℕ} {S : Type} [Fintype S]

lemma prob_nonneg (μ : SignalingStructure n S) (E : Outcome n S → Prop) : 0 ≤ prob μ E := by
  unfold prob
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs
  · exact μ.nonneg ω
  · exact le_rfl

lemma prob_congr (μ : SignalingStructure n S) {E F : Outcome n S → Prop}
    (h : ∀ ω, E ω ↔ F ω) : prob μ E = prob μ F := by
  have : E = F := funext fun ω => propext (h ω)
  rw [this]

lemma expectOn_congr (μ : SignalingStructure n S) {f g : Outcome n S → ℝ}
    {E F : Outcome n S → Prop}
    (h : ∀ ω, E ω ↔ F ω) (hfg : ∀ ω, F ω → f ω = g ω) : expectOn μ f E = expectOn μ g F := by
  unfold expectOn
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hF : F ω
  · rw [if_pos ((h ω).2 hF), if_pos hF, hfg ω hF]
  · rw [if_neg (fun hE => hF ((h ω).1 hE)), if_neg hF]

lemma prob_mono (μ : SignalingStructure n S) {E F : Outcome n S → Prop}
    (h : ∀ ω, E ω → F ω) : prob μ E ≤ prob μ F := by
  unfold prob
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hE : E ω
  · rw [if_pos hE, if_pos (h ω hE)]
  · rw [if_neg hE]
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl

lemma w_eq_zero_of_prob_eq_zero (μ : SignalingStructure n S) {E : Outcome n S → Prop}
    (h : prob μ E = 0) (ω : Outcome n S) (hω : E ω) : μ.w ω = 0 := by
  unfold prob at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => by
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl)).1 h ω (Finset.mem_univ _)
  simpa [hω] using this

lemma expectOn_eq_zero_of_prob_eq_zero (μ : SignalingStructure n S) (f : Outcome n S → ℝ)
    {E : Outcome n S → Prop} (h : prob μ E = 0) : expectOn μ f E = 0 := by
  unfold expectOn
  refine Finset.sum_eq_zero fun ω _ => ?_
  split_ifs with hE
  · rw [w_eq_zero_of_prob_eq_zero μ h ω hE, zero_mul]
  · rfl

lemma expectOn_split_sig (μ : SignalingStructure n S) (i : Fin n) (f : Outcome n S → ℝ)
    (E : Outcome n S → Prop) :
    expectOn μ f E = ∑ s : S, expectOn μ f (fun ω => E ω ∧ sig i ω = s) := by
  classical
  unfold expectOn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hE : E ω
  · simp only [hE, true_and, if_true]
    rw [Finset.sum_eq_single (sig i ω)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · simp [hE]

/-- conditional sums over the information at round `i`. -/
lemma expectOn_info (μ : SignalingStructure n S) (i : Fin n) (F : Info n S i → ℝ)
    (E : Outcome n S → Prop) :
    expectOn μ (fun ω => F (info i ω)) E =
      ∑ x, F x * prob μ (fun ω => info i ω = x ∧ E ω) := by
  classical
  unfold expectOn prob
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hE : E ω
  · simp only [hE, and_true, if_true]
    rw [Finset.sum_eq_single (info i ω)]
    · simp [mul_comm]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · simp [hE]

lemma prob_eq_expectOn_one (μ : SignalingStructure n S) (E : Outcome n S → Prop) :
    prob μ E = expectOn μ (fun _ => 1) E := by
  unfold prob expectOn
  simp

/-! ### Telescoping -/

lemma tele_nat (a : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range k, a j * ∏ l ∈ Finset.range j, (1 - a l) =
      1 - ∏ j ∈ Finset.range k, (1 - a j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Finset.prod_range_succ]
    ring

lemma sum_Iio_fin {i : Fin n} (G : ℕ → ℝ) :
    ∑ j ∈ Finset.Iio i, G j.val = ∑ k ∈ Finset.range i.val, G k := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.sum_map]
  rfl

lemma prod_Iio_fin {i : Fin n} (G : ℕ → ℝ) :
    ∏ j ∈ Finset.Iio i, G j.val = ∏ k ∈ Finset.range i.val, G k := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.prod_map]
  rfl

lemma tele_fin (g : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ Finset.Iio i, g j * ∏ l ∈ Finset.Iio j, (1 - g l) =
      1 - ∏ j ∈ Finset.Iio i, (1 - g j) := by
  set a : ℕ → ℝ := fun k => if h : k < n then g ⟨k, h⟩ else 0 with ha
  have hg : ∀ j : Fin n, g j = a j.val := fun j => by simp [ha, j.isLt]
  have h1 : ∀ j : Fin n, ∏ l ∈ Finset.Iio j, (1 - g l) = ∏ k ∈ Finset.range j.val, (1 - a k) := by
    intro j
    rw [← prod_Iio_fin (fun k => 1 - a k)]
    simp_rw [hg]
  simp_rw [h1, hg]
  rw [sum_Iio_fin (fun k => a k * ∏ l ∈ Finset.range k, (1 - a l))]
  try rw [prod_Iio_fin (fun k => 1 - a k)]
  exact tele_nat a _

/-! ### Information structure -/

lemma emb_last (i : Fin n) : emb i (Fin.last i.val) = i := by
  ext; simp [emb]

lemma lastSignal_info (i : Fin n) (ω : Outcome n S) : lastSignal (info i ω) = sig i ω := by
  simp [lastSignal, info, emb_last, sig]

lemma bestSoFar_info (i : Fin n) (ω : Outcome n S) :
    bestSoFar (info i ω) = true ↔ T i ω := by
  simp only [bestSoFar, info, emb_last, decide_eq_true_eq, T]
  constructor
  · intro h j hj
    have := h ⟨j.val, by have := hj; rw [Fin.lt_def] at this; omega⟩
    have he : emb i ⟨j.val, by rw [Fin.lt_def] at hj; omega⟩ = j := by ext; simp [emb]
    rw [he] at this
    exact this
  · intro h a
    by_cases ha : a.val < i.val
    · have he : emb i a = ⟨a.val, by omega⟩ := by ext; simp [emb]
      rw [he]
      exact h _ (by rw [Fin.lt_def]; exact ha)
    · have he : emb i a = i := by ext; simp [emb]; omega
      rw [he]

/-- restriction of round-`i` information to round `j` (meaningful for `j ≤ i`). -/
def res (i j : Fin n) (x : Info n S i) : Info n S j :=
  (fun a b => x.1 ⟨min a.val i.val, by omega⟩ ⟨min b.val i.val, by omega⟩,
    fun a => x.2 ⟨min a.val i.val, by omega⟩)

lemma info_res {i j : Fin n} (h : j ≤ i) (ω : Outcome n S) :
    info j ω = res i j (info i ω) := by
  have hle : j.val ≤ i.val := h
  have he : ∀ a : Fin (j.val + 1),
      emb i ⟨min a.val i.val, by omega⟩ = emb j a := by
    intro a
    ext
    simp [emb]
    omega
  simp only [info, res, he]

lemma pickProb_factor (q : Policy n S) (i : Fin n) :
    ∃ F : Info n S i → ℝ, ∀ ω, pickProb q i ω = F (info i ω) := by
  refine ⟨fun x => q i x * ∏ j ∈ Finset.Iio i, (1 - q j (res i j x)), fun ω => ?_⟩
  simp only [pickProb]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [info_res (le_of_lt (Finset.mem_Iio.1 hj)) ω]

lemma pickProb_nonneg {q : Policy n S} (hq : ValidPolicy q) (i : Fin n) (ω : Outcome n S) :
    0 ≤ pickProb q i ω :=
  mul_nonneg (hq _ _).1 (Finset.prod_nonneg fun j _ => by linarith [(hq j (info j ω)).2])

lemma sum_pickProb (q : Policy n S) (i : Fin n) (ω : Outcome n S) :
    ∑ j ∈ Finset.Iio i, pickProb q j ω = 1 - ∏ j ∈ Finset.Iio i, (1 - q j (info j ω)) :=
  tele_fin (fun j => q j (info j ω)) i

lemma pickProb_le {q : Policy n S} (hq : ValidPolicy q) (i : Fin n) (ω : Outcome n S) :
    pickProb q i ω ≤ 1 - ∑ j ∈ Finset.Iio i, pickProb q j ω := by
  rw [sum_pickProb]
  simp only [pickProb, sub_sub_cancel]
  have h0 : 0 ≤ ∏ j ∈ Finset.Iio i, (1 - q j (info j ω)) :=
    Finset.prod_nonneg fun j _ => by linarith [(hq j (info j ω)).2]
  have := (hq i (info i ω)).2
  nlinarith

/-! ### Expectation calculus -/

lemma expectOn_eq (μ : SignalingStructure n S) (f : Outcome n S → ℝ) (E : Outcome n S → Prop) :
    expectOn μ f E = ∑ ω, μ.w ω * (if E ω then f ω else 0) := by
  unfold expectOn
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs <;> simp

lemma expectOn_add (μ : SignalingStructure n S) (f g : Outcome n S → ℝ) (E : Outcome n S → Prop) :
    expectOn μ (fun ω => f ω + g ω) E = expectOn μ f E + expectOn μ g E := by
  simp only [expectOn_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs <;> ring

lemma expectOn_const_mul (μ : SignalingStructure n S) (c : ℝ) (f : Outcome n S → ℝ)
    (E : Outcome n S → Prop) :
    expectOn μ (fun ω => c * f ω) E = c * expectOn μ f E := by
  simp only [expectOn_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs <;> ring

lemma expectOn_sum (μ : SignalingStructure n S) {ι : Type} (t : Finset ι) (f : ι → Outcome n S → ℝ)
    (E : Outcome n S → Prop) :
    expectOn μ (fun ω => ∑ j ∈ t, f j ω) E = ∑ j ∈ t, expectOn μ (f j) E := by
  simp only [expectOn_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← Finset.mul_sum]
  split_ifs <;> simp

lemma expectOn_mono (μ : SignalingStructure n S) {f g : Outcome n S → ℝ} (E : Outcome n S → Prop)
    (h : ∀ ω, E ω → f ω ≤ g ω) : expectOn μ f E ≤ expectOn μ g E := by
  simp only [expectOn_eq]
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs with hE
  · exact mul_le_mul_of_nonneg_left (h ω hE) (μ.nonneg ω)
  · exact le_rfl

lemma expectOn_mono_event (μ : SignalingStructure n S) {f : Outcome n S → ℝ}
    {E F : Outcome n S → Prop} (hf : ∀ ω, 0 ≤ f ω)
    (h : ∀ ω, E ω → F ω) : expectOn μ f E ≤ expectOn μ f F := by
  simp only [expectOn_eq]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hE : E ω
  · rw [if_pos hE, if_pos (h ω hE)]
  · rw [if_neg hE, mul_zero]
    split_ifs
    · exact mul_nonneg (μ.nonneg ω) (hf ω)
    · simp

lemma expectOn_nonneg (μ : SignalingStructure n S) {f : Outcome n S → ℝ} (E : Outcome n S → Prop)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expectOn μ f E := by
  simp only [expectOn_eq]
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs
  · exact mul_nonneg (μ.nonneg ω) (hf ω)
  · simp

lemma isTop_T {i : Fin n} {ω : Outcome n S} (h : SecretaryAdvice.Memoryless.IsTop i ω) :
    T i ω := by
  intro j _
  unfold SecretaryAdvice.Memoryless.IsTop at h
  rw [Fin.le_def]
  have := (ω.1 j).isLt
  omega

/-! ### Lifted NF and HI -/

lemma nf_lift (μ : SignalingStructure n S) (hNF : NonFiltering μ) {i j : Fin n} (hji : j < i)
    (F : Info n S j → ℝ) (s' s : S) :
    expectOn μ (fun ω => F (info j ω)) (fun ω => T j ω ∧ sig j ω = s') *
        prob μ (fun ω => T j ω ∧ sig j ω = s' ∧ T i ω ∧ sig i ω = s) =
      expectOn μ (fun ω => F (info j ω)) (fun ω => T j ω ∧ sig j ω = s' ∧ T i ω ∧ sig i ω = s) *
        prob μ (fun ω => T j ω ∧ sig j ω = s') := by
  rw [expectOn_info, expectOn_info, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, mul_assoc, hNF i j hji x s' s]

lemma hi_lift (μ : SignalingStructure n S) (hHI : HistoryIrrelevance μ) (i : Fin n)
    (F : Info n S i → ℝ) (s : S) (b : Bool) :
    expectOn μ (fun ω => F (info i ω)) (fun ω => IsTop i ω ∧ (T i ω ↔ b = true) ∧ sig i ω = s) *
        prob μ (fun ω => (T i ω ↔ b = true) ∧ sig i ω = s) =
      expectOn μ (fun ω => F (info i ω)) (fun ω => (T i ω ↔ b = true) ∧ sig i ω = s) *
        prob μ (fun ω => IsTop i ω ∧ (T i ω ↔ b = true) ∧ sig i ω = s) := by
  rw [expectOn_info, expectOn_info, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, mul_assoc, hHI i x s b]

/-- NF consequence: conditional expectation of a round-`j` quantity given `(T_j, s_j)` is unchanged
by further conditioning on `(T_i, s_i)`. -/
lemma nf_cons (μ : SignalingStructure n S) (hNF : NonFiltering μ) {i j : Fin n} (hji : j < i)
    (F : Info n S j → ℝ) (s' s : S) :
    expectOn μ (fun ω => F (info j ω)) (fun ω => T j ω ∧ sig j ω = s' ∧ T i ω ∧ sig i ω = s) =
      expectOn μ (fun ω => F (info j ω)) (fun ω => T j ω ∧ sig j ω = s') /
        prob μ (fun ω => T j ω ∧ sig j ω = s') *
        prob μ (fun ω => T j ω ∧ sig j ω = s' ∧ T i ω ∧ sig i ω = s) := by
  by_cases hP : prob μ (fun ω => T j ω ∧ sig j ω = s') = 0
  · rw [hP, div_zero, zero_mul]
    apply expectOn_eq_zero_of_prob_eq_zero
    have := prob_mono μ (E := fun ω => T j ω ∧ sig j ω = s' ∧ T i ω ∧ sig i ω = s)
      (F := fun ω => T j ω ∧ sig j ω = s') (fun ω h => ⟨h.1, h.2.1⟩)
    linarith [prob_nonneg μ (fun ω => T j ω ∧ sig j ω = s' ∧ T i ω ∧ sig i ω = s)]
  · rw [div_mul_eq_mul_div, nf_lift μ hNF hji F s' s, mul_div_assoc, div_self hP, mul_one]

/-- HI consequence: `E[F(info_i); r_i = n, s_i = s] = E[F(info_i) | T_i, s_i = s] · a(i, s)`. -/
lemma hi_cons (μ : SignalingStructure n S) (hHI : HistoryIrrelevance μ) (i : Fin n)
    (F : Info n S i → ℝ) (s : S) :
    expectOn μ (fun ω => F (info i ω)) (fun ω => IsTop i ω ∧ sig i ω = s) =
      expectOn μ (fun ω => F (info i ω)) (fun ω => T i ω ∧ sig i ω = s) /
        prob μ (fun ω => T i ω ∧ sig i ω = s) * a μ i s := by
  have h := hi_lift μ hHI i F s true
  have e1 : expectOn μ (fun ω => F (info i ω))
      (fun ω => IsTop i ω ∧ (T i ω ↔ true = true) ∧ sig i ω = s) =
      expectOn μ (fun ω => F (info i ω)) (fun ω => IsTop i ω ∧ sig i ω = s) :=
    expectOn_congr μ (fun ω => by
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by simp [isTop_T h1], h3⟩) (fun _ _ => rfl)
  have e2 : prob μ (fun ω => (T i ω ↔ true = true) ∧ sig i ω = s) =
      prob μ (fun ω => T i ω ∧ sig i ω = s) := prob_congr μ (fun ω => by simp)
  have e3 : expectOn μ (fun ω => F (info i ω)) (fun ω => (T i ω ↔ true = true) ∧ sig i ω = s) =
      expectOn μ (fun ω => F (info i ω)) (fun ω => T i ω ∧ sig i ω = s) :=
    expectOn_congr μ (fun ω => by simp) (fun _ _ => rfl)
  have e4 : prob μ (fun ω => IsTop i ω ∧ (T i ω ↔ true = true) ∧ sig i ω = s) = a μ i s := by
    unfold a
    exact prob_congr μ (fun ω => by
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by simp [isTop_T h1], h3⟩)
  rw [e1, e2, e3, e4] at h
  by_cases hP : prob μ (fun ω => T i ω ∧ sig i ω = s) = 0
  · rw [hP, div_zero, zero_mul]
    apply expectOn_eq_zero_of_prob_eq_zero
    have := prob_mono μ (E := fun ω => IsTop i ω ∧ sig i ω = s)
      (F := fun ω => T i ω ∧ sig i ω = s) (fun ω h => ⟨isTop_T h.1, h.2⟩)
    linarith [prob_nonneg μ (fun ω => IsTop i ω ∧ sig i ω = s)]
  · field_simp
    linarith

end SMA

open SecretaryAdvice.Memoryless

namespace SMA

open Classical

set_option linter.unusedSectionVars false

variable {n : ℕ} {S : Type} [Fintype S]

theorem eq2 (μ : SignalingStructure n S)
    (hHI : HistoryIrrelevance μ) (i : Fin n) (x : Info n S i) :
    prob μ (fun ω => SecretaryAdvice.Memoryless.IsTop i ω ∧ info i ω = x) *
        prob μ (fun ω => (T i ω ↔ bestSoFar x = true) ∧ sig i ω = lastSignal x) =
      prob μ (fun ω => info i ω = x) *
        prob μ (fun ω => SecretaryAdvice.Memoryless.IsTop i ω ∧ (T i ω ↔ bestSoFar x = true) ∧
          sig i ω = lastSignal x) := by
  have h := hHI i x (lastSignal x) (bestSoFar x)
  have hx : ∀ ω, info i ω = x → (T i ω ↔ bestSoFar x = true) ∧ sig i ω = lastSignal x := by
    intro ω hω
    subst hω
    exact ⟨(bestSoFar_info i ω).symm, (lastSignal_info i ω).symm⟩
  have e1 : prob μ (fun ω => info i ω = x ∧ SecretaryAdvice.Memoryless.IsTop i ω ∧
      (T i ω ↔ bestSoFar x = true) ∧ sig i ω = lastSignal x) =
      prob μ (fun ω => SecretaryAdvice.Memoryless.IsTop i ω ∧ info i ω = x) :=
    prob_congr μ fun ω => ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, hx ω h.2⟩⟩
  have e2 : prob μ (fun ω => info i ω = x ∧ (T i ω ↔ bestSoFar x = true) ∧
      sig i ω = lastSignal x) = prob μ (fun ω => info i ω = x) :=
    prob_congr μ fun ω => ⟨fun h => h.1, fun h => ⟨h, hx ω h⟩⟩
  rw [e1, e2] at h
  exact h

lemma expectOn_ind (μ : SignalingStructure n S) (i : Fin n) (A : Set (Info n S i))
    (E : Outcome n S → Prop) :
    expectOn μ (fun ω => if info i ω ∈ A then (1 : ℝ) else 0) E =
      prob μ (fun ω => info i ω ∈ A ∧ E ω) := by
  unfold expectOn prob
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hA : info i ω ∈ A <;> by_cases hE : E ω <;> simp [hA, hE]

theorem eq3 (μ : SignalingStructure n S)
    (hHI : HistoryIrrelevance μ) (i : Fin n) (A : Set (Info n S i)) (s : S) :
    prob μ (fun ω => info i ω ∈ A ∧ sig i ω = s ∧ SecretaryAdvice.Memoryless.IsTop i ω) *
        prob μ (fun ω => T i ω ∧ sig i ω = s) =
      prob μ (fun ω => info i ω ∈ A ∧ T i ω ∧ sig i ω = s) *
        prob μ (fun ω => sig i ω = s ∧ SecretaryAdvice.Memoryless.IsTop i ω) := by
  have h := hi_lift μ hHI i (fun x => if x ∈ A then (1 : ℝ) else 0) s true
  rw [expectOn_ind, expectOn_ind] at h
  have e1 : prob μ (fun ω => info i ω ∈ A ∧ SecretaryAdvice.Memoryless.IsTop i ω ∧
      (T i ω ↔ true = true) ∧ sig i ω = s) =
      prob μ (fun ω => info i ω ∈ A ∧ sig i ω = s ∧ SecretaryAdvice.Memoryless.IsTop i ω) :=
    prob_congr μ fun ω => ⟨fun h => ⟨h.1, h.2.2.2, h.2.1⟩,
      fun h => ⟨h.1, h.2.2, by simp [isTop_T h.2.2], h.2.1⟩⟩
  have e2 : prob μ (fun ω => (T i ω ↔ true = true) ∧ sig i ω = s) =
      prob μ (fun ω => T i ω ∧ sig i ω = s) := prob_congr μ fun ω => by simp
  have e3 : prob μ (fun ω => info i ω ∈ A ∧ (T i ω ↔ true = true) ∧ sig i ω = s) =
      prob μ (fun ω => info i ω ∈ A ∧ T i ω ∧ sig i ω = s) := prob_congr μ fun ω => by simp
  have e4 : prob μ (fun ω => SecretaryAdvice.Memoryless.IsTop i ω ∧ (T i ω ↔ true = true) ∧
      sig i ω = s) = prob μ (fun ω => sig i ω = s ∧ SecretaryAdvice.Memoryless.IsTop i ω) :=
    prob_congr μ fun ω => ⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, by simp [isTop_T h.2], h.1⟩⟩
  rw [e1, e2, e3, e4] at h
  exact h

theorem bsf (μ : SignalingStructure n S)
    (q : Policy n S) (hq : ValidPolicy q) :
    ∃ q' : Policy n S, ValidPolicy q' ∧
      (∀ (i : Fin n) (x : Info n S i), bestSoFar x = false → q' i x = 0) ∧
      win μ q ≤ win μ q' := by
  refine ⟨fun i x => if bestSoFar x = true then q i x else 0, ?_, ?_, ?_⟩
  · intro i x
    simp only
    split_ifs
    · exact hq i x
    · exact ⟨le_rfl, zero_le_one⟩
  · intro i x hx
    simp [hx]
  · unfold win
    refine Finset.sum_le_sum fun i _ => expectOn_mono μ _ fun ω hω => ?_
    have hT : T i ω := isTop_T hω
    unfold pickProb
    simp only []
    rw [if_pos ((bestSoFar_info i ω).2 hT)]
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun j _ => ?_) (fun j _ => ?_))
      (hq i _).1
    · linarith [(hq j (info j ω)).2]
    · split_ifs
      · exact le_rfl
      · linarith [(hq j (info j ω)).1]

end SMA

open SecretaryAdvice.Memoryless in
theorem solution {n : ℕ} {S : Type} [Fintype S] (μ : SignalingStructure n S)
    (hHI : HistoryIrrelevance μ) (i : Fin n) (x : Info n S i) :
    prob μ (fun ω => IsTop i ω ∧ info i ω = x) *
        prob μ (fun ω => (T i ω ↔ bestSoFar x = true) ∧ sig i ω = lastSignal x) =
      prob μ (fun ω => info i ω = x) *
        prob μ (fun ω => IsTop i ω ∧ (T i ω ↔ bestSoFar x = true) ∧ sig i ω = lastSignal x) :=
  SMA.eq2 μ hHI i x
