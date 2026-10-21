-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P44.noiselessPhotonZeroError
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T03:18:11.98302+00:00
-- url     : https://prove2.me/submissions/3f10d47f-9a4f-4edf-90fb-720712c31b43

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44
noncomputable section

open QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P16 (opCoeff)

open Finset

/-- terms of the binomial expansion of (a+b)^N -/
def g65e_t (a b N j : ℕ) : ℝ := (N.choose j : ℝ) * (a : ℝ) ^ j * (b : ℝ) ^ (N - j)

theorem g65e_t_nonneg (a b N j : ℕ) : 0 ≤ g65e_t a b N j := by
  unfold g65e_t; positivity

theorem g65e_ratio (a b N j : ℕ) (hj : j < N) :
    g65e_t a b N (j + 1) * ((j + 1 : ℕ) * b) = g65e_t a b N j * ((N - j : ℕ) * a) := by
  unfold g65e_t
  have h1 := Nat.choose_succ_right_eq N j
  have h1' : (N.choose (j+1) : ℝ) * ((j + 1 : ℕ) : ℝ) = (N.choose j : ℝ) * ((N - j : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h2 : N - j = (N - (j + 1)) + 1 := by omega
  have hb' : (b : ℝ) ^ (N - j) = (b : ℝ) ^ (N - (j + 1)) * b := by rw [h2, pow_succ]
  rw [hb', pow_succ]
  linear_combination (a : ℝ) ^ j * (a : ℝ) * (b : ℝ) ^ (N - (j + 1)) * (b : ℝ) * h1'

theorem g65e_up (a b : ℕ) (hb : 0 < b) (j : ℕ) (hj : j < a) :
    g65e_t a b (a + b) j ≤ g65e_t a b (a + b) (j + 1) := by
  have hr := g65e_ratio a b (a + b) j (by omega)
  have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) * b := by positivity
  have hc : ((j + 1 : ℕ) : ℝ) * b ≤ ((a + b - j : ℕ) : ℝ) * a := by
    have : (j + 1) * b ≤ (a + b - j) * a := by
      have h3 : b + 1 ≤ a + b - j := by omega
      calc (j + 1) * b ≤ a * b := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (b + 1) * a := by nlinarith
        _ ≤ (a + b - j) * a := Nat.mul_le_mul_right _ h3
    exact_mod_cast this
  have h0 := g65e_t_nonneg a b (a + b) j
  by_contra hcon
  push Not at hcon
  have : g65e_t a b (a + b) (j + 1) * (((j + 1 : ℕ) : ℝ) * b) <
      g65e_t a b (a + b) j * (((j + 1 : ℕ) : ℝ) * b) := mul_lt_mul_of_pos_right hcon hpos
  nlinarith [mul_le_mul_of_nonneg_left hc h0]

theorem g65e_down (a b : ℕ) (ha : 0 < a) (j : ℕ) (hj : a ≤ j) :
    g65e_t a b (a + b) (j + 1) ≤ g65e_t a b (a + b) j := by
  rcases Nat.lt_or_ge j (a + b) with hjN | hjN
  · have hr := g65e_ratio a b (a + b) j hjN
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) * b ∨ b = 0 := by
      rcases Nat.eq_zero_or_pos b with h | h
      · exact Or.inr h
      · left; positivity
    rcases hpos with hpos | hb0
    · have hc : ((a + b - j : ℕ) : ℝ) * a ≤ ((j + 1 : ℕ) : ℝ) * b := by
        have : (a + b - j) * a ≤ (j + 1) * b := by
          calc (a + b - j) * a ≤ b * a := Nat.mul_le_mul_right _ (by omega)
            _ = a * b := by ring
            _ ≤ (j + 1) * b := Nat.mul_le_mul_right _ (by omega)
        exact_mod_cast this
      have h0 := g65e_t_nonneg a b (a + b) j
      by_contra hcon
      push Not at hcon
      have : g65e_t a b (a + b) j * (((j + 1 : ℕ) : ℝ) * b) <
          g65e_t a b (a + b) (j + 1) * (((j + 1 : ℕ) : ℝ) * b) := mul_lt_mul_of_pos_right hcon hpos
      nlinarith [mul_le_mul_of_nonneg_left hc h0]
    · subst hb0; omega
  · unfold g65e_t
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp only [Nat.cast_zero, zero_mul]
    exact g65e_t_nonneg a b _ j

theorem g65e_max (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    g65e_t a b (a + b) j ≤ g65e_t a b (a + b) a := by
  rcases le_or_gt j a with hj | hj
  · have key : ∀ k, g65e_t a b (a + b) (a - k) ≤ g65e_t a b (a + b) a := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rcases Nat.lt_or_ge k a with hk | hk
        · have := g65e_up a b hb (a - (k + 1)) (by omega)
          have e : a - (k + 1) + 1 = a - k := by omega
          rw [e] at this; linarith
        · have e : a - (k + 1) = a - k := by omega
          rw [e]; exact ih
    have := key (a - j)
    rwa [show a - (a - j) = j by omega] at this
  · have hj' : a ≤ j := hj.le
    clear hj
    induction j, hj' using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact (g65e_down a b ha k hk).trans ih

/-- Binomial max-term lower bound. -/
theorem g65e_binom (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((a + b : ℕ) : ℝ) ^ (a + b) ≤ ((a + b + 1 : ℕ) : ℝ) * ((a + b).choose a : ℝ) * (a : ℝ) ^ a * (b : ℝ) ^ b := by
  have hsum : ((a + b : ℕ) : ℝ) ^ (a + b) = ∑ j ∈ range (a + b + 1), g65e_t a b (a + b) j := by
    push_cast
    rw [add_pow]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold g65e_t; ring
  rw [hsum]
  calc ∑ j ∈ range (a + b + 1), g65e_t a b (a + b) j ≤ ∑ j ∈ range (a + b + 1), g65e_t a b (a + b) a :=
        Finset.sum_le_sum (fun j _ => g65e_max a b ha hb j)
    _ = ((a + b + 1 : ℕ) : ℝ) * ((a + b).choose a : ℝ) * (a : ℝ) ^ a * (b : ℝ) ^ b := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        unfold g65e_t
        rw [show a + b - a = b by omega]; ring

/-- Gibbs inequality. -/
theorem g65e_gibbs (E p : ℝ) (hE : 0 < E) (hp0 : 0 < p) (hp1 : p < 1) :
    (E + 1) * Real.log (E + 1) - E * Real.log E ≤ -E * Real.log p - Real.log (1 - p) := by
  have h1 := Real.one_sub_inv_le_log_of_pos (x := E / ((E + 1) * p)) (by positivity)
  have h2 := Real.one_sub_inv_le_log_of_pos (x := 1 / ((E + 1) * (1 - p))) (by
    have : 0 < 1 - p := by linarith
    positivity)
  have hq : 0 < 1 - p := by linarith
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)] at h1
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_one] at h2
  rw [inv_div] at h1
  rw [inv_div, div_one] at h2
  have e1 : E * (1 - (E + 1) * p / E) = E - (E + 1) * p := by field_simp
  have hm := mul_le_mul_of_nonneg_left h1 hE.le
  rw [e1] at hm
  nlinarith

/-- log of binomial lower bound with a ≥ tE, b ≥ t. -/
theorem g65e_logbinom (E t : ℝ) (hE : 0 < E) (ht : 0 ≤ t) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hat : t * E ≤ a) (hbt : t ≤ b) :
    t * ((E + 1) * Real.log (E + 1) - E * Real.log E) - Real.log ((a + b + 1 : ℕ) : ℝ)
      ≤ Real.log ((a + b).choose a : ℝ) := by
  have hN : (0 : ℝ) < ((a + b : ℕ) : ℝ) := by positivity
  set p : ℝ := (a : ℝ) / ((a + b : ℕ) : ℝ)
  have hp0 : 0 < p := by positivity
  have hp1 : p < 1 := by
    rw [div_lt_one hN]; push_cast; have : (0:ℝ) < b := by exact_mod_cast hb
    linarith
  have h1p : 1 - p = (b : ℝ) / ((a + b : ℕ) : ℝ) := by
    simp only [p]; field_simp; push_cast; ring
  have hB := g65e_binom a b ha hb
  -- divide
  have key : 1 ≤ ((a + b + 1 : ℕ) : ℝ) * ((a + b).choose a : ℝ) * p ^ a * (1 - p) ^ b := by
    rw [h1p]; simp only [p]
    rw [div_pow, div_pow]
    have hNN : (0:ℝ) < ((a + b : ℕ) : ℝ) ^ a * ((a + b : ℕ) : ℝ) ^ b := by positivity
    rw [show ((a + b + 1 : ℕ) : ℝ) * ((a + b).choose a : ℝ) * ((a : ℝ) ^ a / ((a + b : ℕ) : ℝ) ^ a) *
        ((b : ℝ) ^ b / ((a + b : ℕ) : ℝ) ^ b) = (((a + b + 1 : ℕ) : ℝ) * ((a + b).choose a : ℝ) *
        (a : ℝ) ^ a * (b : ℝ) ^ b) / (((a + b : ℕ) : ℝ) ^ a * ((a + b : ℕ) : ℝ) ^ b) by
          field_simp]
    rw [le_div_iff₀ hNN, one_mul, ← pow_add]; exact hB
  have hC : (0 : ℝ) < ((a + b).choose a : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hlog := Real.log_le_log (by norm_num) key
  rw [Real.log_one, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hlp : Real.log p < 0 := Real.log_neg hp0 hp1
  have hlq : Real.log (1 - p) < 0 := Real.log_neg (by linarith) (by linarith)
  have hg := g65e_gibbs E p hE hp0 hp1
  have e1 : t * E * Real.log p ≥ (a : ℝ) * Real.log p := by nlinarith
  have e2 : t * Real.log (1 - p) ≥ (b : ℝ) * Real.log (1 - p) := by nlinarith
  have e3 := mul_le_mul_of_nonneg_left hg ht
  nlinarith

theorem g65e_eventually (E R : ℝ) (hE : 0 ≤ E)
    (hR : R < (E + 1) * Real.log (E + 1) - E * Real.log E) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      Real.exp ((n : ℝ) * R) ≤ ((n + ⌊(n : ℝ) * E⌋₊ - 1).choose ⌊(n : ℝ) * E⌋₊ : ℝ) := by
  rcases hE.eq_or_lt with h0 | hE
  · subst h0
    simp at hR
    refine ⟨0, fun n _ => ?_⟩
    simp only [mul_zero, Nat.floor_zero, Nat.choose_zero_right, Nat.cast_one]
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hR.le
  set G := (E + 1) * Real.log (E + 1) - E * Real.log E
  set δ := G - R
  have hδ : 0 < δ := by simp only [δ]; linarith
  set K := (1 + 1 / E) * G + Real.log (E + 1) - 1 - Real.log (δ / 2)
  refine ⟨⌈(E + 2) / E⌉₊ + ⌈2 * |K| / δ⌉₊ + 2, fun n hn => ?_⟩
  have hn1 : (E + 2) / E ≤ (n : ℝ) := by
    have := Nat.le_ceil ((E + 2) / E)
    have : ((⌈(E + 2) / E⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈(E + 2) / E⌉₊ ≤ n)
    linarith
  have hn2 : 2 * |K| / δ ≤ (n : ℝ) := by
    have := Nat.le_ceil (2 * |K| / δ)
    have : ((⌈2 * |K| / δ⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈2 * |K| / δ⌉₊ ≤ n)
    linarith
  have hn3 : 2 ≤ n := by omega
  have hnE : E + 2 ≤ (n : ℝ) * E := by
    rw [div_le_iff₀ hE] at hn1; linarith
  set m := ⌊(n : ℝ) * E⌋₊
  have hm1 : (n : ℝ) * E - 1 < m := Nat.sub_one_lt_floor _
  have hm2 : (m : ℝ) ≤ n * E := Nat.floor_le (by positivity)
  have hmpos : 0 < m := by
    have : (0 : ℝ) < m := by linarith
    exact_mod_cast this
  set t : ℝ := n - 1 - 1 / E
  have ht : 0 ≤ t := by
    simp only [t]
    have : 1 / E ≤ (n : ℝ) - 1 := by
      rw [div_le_iff₀ hE]; linarith
    linarith
  have htE : t * E ≤ m := by
    simp only [t]
    have : (n - 1 - 1 / E) * E = n * E - E - 1 := by field_simp
    rw [this]; linarith
  have hb : t ≤ ((n - 1 : ℕ) : ℝ) := by
    simp only [t]; rw [Nat.cast_sub (by omega)]; push_cast
    have : 0 < 1 / E := by positivity
    linarith
  have hL := g65e_logbinom E t hE ht m (n - 1) hmpos (by omega) htE hb
  rw [show n + m - 1 = m + (n - 1) by omega]
  have hC : (0 : ℝ) < ((m + (n - 1)).choose m : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  rw [← Real.exp_log hC, Real.exp_le_exp]
  have hcast : ((m + (n - 1) + 1 : ℕ) : ℝ) = m + n := by
    rw [show m + (n - 1) + 1 = m + n by omega]; push_cast; ring
  rw [hcast] at hL
  -- log (m + n) ≤ log n + log (E + 1)
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog1 : Real.log ((m : ℝ) + n) ≤ Real.log n + Real.log (E + 1) := by
    rw [← Real.log_mul hnpos.ne' (by positivity)]
    apply Real.log_le_log (by positivity); nlinarith
  have hlog2 : Real.log n ≤ δ / 2 * n - 1 - Real.log (δ / 2) := by
    have := Real.log_le_sub_one_of_pos (x := δ / 2 * n) (by positivity)
    rw [Real.log_mul (by positivity) hnpos.ne'] at this
    linarith
  have hK : K ≤ δ / 2 * n := by
    have : 2 * |K| ≤ δ * n := by rw [div_le_iff₀ hδ] at hn2; linarith
    have := le_abs_self K
    linarith
  have htG : t * G = n * G - (1 + 1 / E) * G := by simp only [t]; ring
  have hR' : (n : ℝ) * R = n * G - n * δ := by simp only [δ]; ring
  nlinarith

theorem g65a_tracePair_rankOne {I : Type} (w u : Hilbert I) :
    tracePair (InnerProductSpace.rankOne ℂ w w) (TC.rankOne u) = ‖inner ℂ w u‖ ^ 2 := by
  unfold tracePair
  have h1 : ∀ i j, opCoeff (InnerProductSpace.rankOne ℂ w w) i j * TC.rankOne u j i =
      (w i * star (u i)) * (star (w j) * u j) := by
    intro i j
    simp only [opCoeff, InnerProductSpace.rankOne_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.inner_single_right]
    simp [QAlgorithms.Papers.Independent.Dependency50.P33.rankOne]
    ring
  simp_rw [h1, tsum_mul_left]
  have h2 : ∑' j, star (w j) * u j = inner ℂ w u := by
    rw [lp.inner_eq_tsum]; exact tsum_congr (fun i => by simp [mul_comm])
  have h3 : ∑' i, w i * star (u i) = inner ℂ u w := by
    rw [lp.inner_eq_tsum]; exact tsum_congr (fun i => by simp)
  rw [h2, tsum_mul_right, h3, ← inner_conj_symm u w]
  rw [mul_comm, Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq]
  norm_cast
theorem g65a_re_eff {I : Type} (u x : Hilbert I) :
    (inner ℂ x (InnerProductSpace.rankOne ℂ u u x)).re = ‖inner ℂ u x‖ ^ 2 := by
  rw [InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm x u,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast


theorem g65e_words (n m M : ℕ) (hM : M ≤ (n + m - 1).choose m) :
    ∃ W : Fin M → (Fin n → ℕ), Function.Injective W ∧ ∀ j, ∑ k, W j k = m := by
  have hc : Fintype.card (Fin M) ≤ Fintype.card (Sym (Fin n) m) := by
    rw [Sym.card_sym_eq_choose]; simpa using hM
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun j k => Multiset.count k (e j : Multiset (Fin n)), ?_, ?_⟩
  · intro x y hxy
    apply e.injective
    apply Sym.coe_injective
    ext k
    exact congrFun hxy k
  · intro j
    rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
    exact (e j).2

theorem g65e_photon0 (m i j : ℕ) : photonOutput 0 m i j = if i = m ∧ j = m then 1 else 0 := by
  unfold photonOutput
  by_cases hij : i = j
  · subst hij
    by_cases him : i = m
    · subst him; simp
    · have : ¬ (i = i ∧ m ≤ i) ∨ (m < i) := by omega
      rcases this with h | h
      · rw [if_neg h, if_neg (by tauto)]
      · rw [if_pos ⟨rfl, h.le⟩, if_neg (by tauto)]
        simp [zero_pow (by omega : i - m ≠ 0)]
  · rw [if_neg (by tauto), if_neg (by omega)]

theorem g65e_wordOutput {n : ℕ} (w : Fin n → ℕ) :
    wordOutput (photonOutput 0) w = TC.rankOne (lp.single 2 w (1 : ℂ)) := by
  funext a b
  simp only [wordOutput, g65e_photon0, QAlgorithms.Papers.Independent.Dependency50.P33.rankOne]
  rw [Fintype.prod_boole]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases ha : a = w <;> by_cases hb : b = w
  · subst ha; subst hb; simp
  · rw [if_neg, if_neg hb]; · simp
    intro h; exact hb (funext fun k => (h k).2)
  · rw [if_neg, if_neg ha]; · simp
    intro h; exact ha (funext fun k => (h k).1)
  · rw [if_neg, if_neg ha]; · simp
    intro h; exact ha (funext fun k => (h k).1)

theorem g65e_orth {J : Type} [DecidableEq J] {M : ℕ} (W : Fin M → J) (hW : Function.Injective W) :
    Orthonormal ℂ (fun j => (lp.single 2 (W j) (1 : ℂ) : Hilbert J)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [lp.inner_single_left, lp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · have : W i ≠ W j := fun e => h (hW e)
    rw [if_neg this, if_neg h]; simp

theorem g65e_zero {n M : ℕ} (hM : 0 < M) (W : Fin M → (Fin n → ℕ)) (hW : Function.Injective W) :
    optimalCollectiveError (fun k => wordOutput (photonOutput 0) (W k)) = 0 := by
  have ho := g65e_orth W hW
  set e : Fin M → Hilbert (Fin n → ℕ) := fun j => lp.single 2 (W j) (1 : ℂ) with he
  let X : Receiver (Fin n → ℕ) M :=
    { effect := fun k => InnerProductSpace.rankOne ℂ (e k) (e k)
      selfAdjoint := fun k => by simp
      positive := fun k v => by rw [g65a_re_eff]; positivity
      subidentity := fun v => by
        simp only [g65a_re_eff]
        have := ho.sum_inner_products_le (s := Finset.univ) v
        simpa [he] using this }
  refine le_antisymm ?_ bot_le
  refine (iInf_le _ X).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_eq_zero]
  unfold collectiveAverageError
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro k _
  simp only [X, g65e_wordOutput]
  rw [g65a_tracePair_rankOne]
  have : ‖e k‖ = 1 := by have := ho.1 k; simpa [he] using this
  rw [inner_self_eq_norm_sq_to_K, this]; simp

theorem solution (E R : ℝ) (hE : 0 ≤ E)
    (hR : R < g E) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      cqError (photonOutput 0) (fun m => (m : ℝ)) E n (natMessagesNats n R) = 0 := by
  obtain ⟨n0, hn0⟩ := g65e_eventually E R hE (by simpa [g] using hR)
  refine ⟨n0 + 1, by omega, fun n hn => ?_⟩
  have hc := hn0 n (by omega)
  set m := ⌊(n : ℝ) * E⌋₊
  set M := natMessagesNats n R
  have hMle : M ≤ (n + m - 1).choose m := by
    simp only [M, natMessagesNats]
    rw [Nat.ceil_le]; exact hc
  have hMpos : 0 < M := by
    simp only [M, natMessagesNats]; exact Nat.ceil_pos.2 (Real.exp_pos _)
  obtain ⟨W, hW, hsum⟩ := g65e_words n m M hMle
  refine le_antisymm ?_ bot_le
  have hcost : ∀ k, wordCost (fun m : ℕ => (m : ℝ)) (W k) ≤ (n : ℝ) * E := by
    intro k
    unfold wordCost
    have : (∑ i, ((W k i : ℕ) : ℝ)) = ((∑ i, W k i : ℕ) : ℝ) := by push_cast; rfl
    rw [this, hsum k]
    exact Nat.floor_le (by positivity)
  refine (iInf_le _ ⟨W, hcost⟩).trans (le_of_eq ?_)
  exact g65e_zero hMpos W hW
