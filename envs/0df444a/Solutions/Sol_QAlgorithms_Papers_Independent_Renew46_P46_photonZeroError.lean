-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P46.photonZeroError
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T03:27:28.368164+00:00
-- url     : https://prove2.me/submissions/e69bfc95-2a16-42f9-9fbe-7192186af0be

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46
noncomputable section

open QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq


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

theorem g65e_ket_apply {I : Type} (i j : I) :
    (constrainedCqKet i : Hilbert I) j = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h; simp [constrainedCqKet]
  · rw [if_neg h]; simp [constrainedCqKet, lp.single_apply, Pi.single_apply, h]

theorem g65e_ext {I : Type} (X Y : constrainedCqOperator I)
    (h : ∀ i j, constrainedCqCoefficient X i j = constrainedCqCoefficient Y i j) : X = Y := by
  have hb : ∀ j, X (constrainedCqKet j) = Y (constrainedCqKet j) := by
    intro j; ext i; exact h i j
  ext1 f
  have hs := lp.hasSum_single (p := 2) (by norm_num) f
  have e : ∀ i, lp.single 2 i (f i) = (f i) • (constrainedCqKet i : Hilbert I) := by
    intro i; ext k
    rw [lp.coeFn_smul, Pi.smul_apply, g65e_ket_apply, lp.single_apply, Pi.single_apply]
    by_cases h1 : k = i
    · subst h1; simp
    · simp [h1, Ne.symm h1]
  simp_rw [e] at hs
  have hX := hs.mapL X
  have hY := hs.mapL Y
  simp only [map_smul, hb] at hX
  simp only [map_smul] at hY
  exact hX.unique hY

theorem g65e_ofCoeff {I : Type} (a : I → I → ℂ) (Y : constrainedCqOperator I)
    (hY : ∀ i j, constrainedCqCoefficient Y i j = a i j) : ofCoefficients a = Y := by
  have hex : ∃ X : constrainedCqOperator I, ∀ i j, constrainedCqCoefficient X i j = a i j := ⟨Y, hY⟩
  unfold ofCoefficients
  rw [dif_pos hex]
  apply g65e_ext
  intro i j
  rw [Classical.choose_spec hex i j, hY]

theorem g65e_coeff_rankOne {I : Type} (u : I) (i j : I) :
    constrainedCqCoefficient (InnerProductSpace.rankOne ℂ (constrainedCqKet u) (constrainedCqKet u) : constrainedCqOperator I) i j
      = if i = u ∧ j = u then 1 else 0 := by
  unfold constrainedCqCoefficient
  rw [InnerProductSpace.rankOne_apply, lp.coeFn_smul, Pi.smul_apply, g65e_ket_apply]
  unfold constrainedCqKet
  rw [lp.inner_single_left, lp.single_apply, Pi.single_apply]
  by_cases h1 : i = u <;> by_cases h2 : j = u
  · simp [h1, h2]
  · simp [h1, h2, Ne.symm h2]
  · simp [h1, h2]
  · simp [h1, h2, Ne.symm h2]

theorem g65e_inner_ket {I : Type} (a : I) (f : Hilbert I) :
    inner ℂ (constrainedCqKet a : Hilbert I) f = f a := by
  unfold constrainedCqKet
  rw [lp.inner_single_left]; simp

theorem g65e_photon_eq (m : ℕ) :
    photonSignal 0 m = InnerProductSpace.rankOne ℂ (constrainedCqKet m) (constrainedCqKet m) := by
  unfold photonSignal
  apply g65e_ofCoeff
  intro i j
  rw [g65e_coeff_rankOne]
  by_cases hij : i = j
  · subst hij
    by_cases him : i = m
    · subst him; simp
    · rw [if_neg (by tauto)]
      by_cases h2 : m ≤ i
      · rw [if_pos ⟨rfl, h2⟩]
        simp [zero_pow (by omega : i - m ≠ 0)]
      · rw [if_neg (by tauto)]
  · rw [if_neg (by omega), if_neg (by tauto)]

theorem g65e_re_eff {I : Type} (u x : Hilbert I) :
    (inner ℂ x (InnerProductSpace.rankOne ℂ u u x)).re = ‖inner ℂ u x‖ ^ 2 := by
  rw [InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm x u,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem g65e_rankOne_pos {I : Type} (u : Hilbert I) :
    QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive
      (InnerProductSpace.rankOne ℂ u u : constrainedCqOperator I) := by
  refine ⟨by simp, fun x => ?_⟩
  rw [g65e_re_eff]; positivity

theorem g65e_rankOne_tc {I : Type} (u : Hilbert I) :
    QAlgorithms.Papers.Independent.Dependency50.P13.IsTraceClass
      (InnerProductSpace.rankOne ℂ u u : constrainedCqOperator I) := by
  refine ⟨fun r => if r = 0 then u else 0, fun r => if r = 0 then u else 0, ?_, ?_⟩
  · apply summable_of_ne_finset_zero (s := {0})
    intro r hr
    simp only [Finset.mem_singleton] at hr
    simp [hr]
  · intro x
    rw [tsum_eq_single 0]
    · simp [InnerProductSpace.rankOne_apply]
    · intro r hr; simp [hr]

theorem g65e_trace_comp {I : Type} (X : constrainedCqOperator I) (w : I) :
    opTrace (X.comp (InnerProductSpace.rankOne ℂ (constrainedCqKet w) (constrainedCqKet w))) =
      X (constrainedCqKet w) w := by
  unfold opTrace constrainedCqCoefficient
  have : ∀ i, (X.comp (InnerProductSpace.rankOne ℂ (constrainedCqKet w) (constrainedCqKet w)))
      (constrainedCqKet i) i = if i = w then X (constrainedCqKet w) w else 0 := by
    intro i
    rw [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, g65e_inner_ket,
      g65e_ket_apply, map_smul, lp.coeFn_smul, Pi.smul_apply]
    by_cases h : w = i
    · subst h; simp
    · simp [h, Ne.symm h]
  simp_rw [this]
  rw [tsum_ite_eq]

theorem g65e_density {I : Type} (w : I) :
    constrainedCqDensity (InnerProductSpace.rankOne ℂ (constrainedCqKet w) (constrainedCqKet w) :
      constrainedCqOperator I) := by
  refine ⟨g65e_rankOne_tc _, g65e_rankOne_pos _, ?_, ?_⟩
  · simp_rw [g65e_coeff_rankOne]
    apply summable_of_ne_finset_zero (s := {w})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [hi]
  · have := g65e_trace_comp (1 : constrainedCqOperator I) w
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] at this
    rw [this]
    simp [g65e_ket_apply]

theorem g65e_hP : ∀ m, constrainedCqDensity (photonSignal 0 m) := by
  intro m; rw [g65e_photon_eq]; exact g65e_density m

theorem g65e_word (hP : ∀ m, constrainedCqDensity (photonSignal 0 m)) (n : ℕ) (u : Fin n → ℕ) :
    wordSignal (stateFamily (photonSignal 0) hP) n u =
      InnerProductSpace.rankOne ℂ (constrainedCqKet u) (constrainedCqKet u) := by
  unfold wordSignal
  apply g65e_ofCoeff
  intro a b
  unfold wordCoefficients
  simp only [stateFamily, g65e_photon_eq, g65e_coeff_rankOne]
  by_cases hab : a = u ∧ b = u
  · rw [if_pos hab]; obtain ⟨rfl, rfl⟩ := hab
    exact (Finset.prod_eq_one fun k _ => if_pos ⟨rfl, rfl⟩).symm
  · rw [if_neg hab]
    have : ∃ k, ¬(a k = u k ∧ b k = u k) := by
      by_contra hc
      push Not at hc
      exact hab ⟨funext fun k => (hc k).1, funext fun k => (hc k).2⟩
    obtain ⟨k, hk⟩ := this
    exact (Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)).symm

theorem g65e_orthK {J : Type} {M : ℕ} (W : Fin M → J) (hW : Function.Injective W) :
    Orthonormal ℂ (fun j => (constrainedCqKet (W j) : Hilbert J)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [g65e_inner_ket, g65e_ket_apply]
  by_cases h : i = j
  · subst h; simp
  · have : W i ≠ W j := fun e => h (hW e)
    rw [if_neg this, if_neg h]

theorem g65e_err_nonneg (hP : ∀ m, constrainedCqDensity (photonSignal 0 m)) (E : ℝ) (n M : ℕ)
    (c : constrainedCqCode (stateFamily (photonSignal 0) hP) (fun m : ℕ => (m : ℝ)) E n M) :
    0 ≤ constrainedCqCodeError c := by
  unfold constrainedCqCodeError
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro k _
  rw [g65e_word, g65e_trace_comp]
  set w := c.word k
  have hs := c.subidentity.2 (constrainedCqKet w)
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, ContinuousLinearMap.sum_apply, inner_sum,
    Complex.sub_re, Complex.re_sum, ContinuousLinearMap.one_apply] at hs
  have h1 : (inner ℂ (constrainedCqKet w : Hilbert (Fin n → ℕ)) (constrainedCqKet w)).re = 1 := by
    rw [g65e_inner_ket, g65e_ket_apply]; simp
  have h2 : (inner ℂ (constrainedCqKet w : Hilbert (Fin n → ℕ)) (c.effect k (constrainedCqKet w))).re ≤
      ∑ j, (inner ℂ (constrainedCqKet w : Hilbert (Fin n → ℕ)) (c.effect j (constrainedCqKet w))).re :=
    Finset.single_le_sum (f := fun j => (inner ℂ (constrainedCqKet w : Hilbert (Fin n → ℕ))
      (c.effect j (constrainedCqKet w))).re) (fun j _ => (c.positive j).2 _) (Finset.mem_univ k)
  rw [g65e_inner_ket] at h2
  linarith

theorem g65e_code_exists (hP : ∀ m, constrainedCqDensity (photonSignal 0 m)) (E : ℝ) (n M : ℕ)
    (hM : 0 < M) (W : Fin M → (Fin n → ℕ)) (hW : Function.Injective W)
    (hcost : ∀ k, wordCost (fun m : ℕ => (m : ℝ)) n (W k) ≤ (n : ℝ) * E) :
    ∃ c : constrainedCqCode (stateFamily (photonSignal 0) hP) (fun m : ℕ => (m : ℝ)) E n M,
      constrainedCqCodeError c = 0 := by
  have ho := g65e_orthK W hW
  refine ⟨constrainedCqCode.mk hM W hcost
    (fun k => InnerProductSpace.rankOne ℂ (constrainedCqKet (W k)) (constrainedCqKet (W k)))
    (fun k => g65e_rankOne_pos _) ⟨?_, ?_⟩, ?_⟩
  · simp [map_sub, map_sum, ContinuousLinearMap.adjoint_one]
  · intro x
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, ContinuousLinearMap.sum_apply, inner_sum,
      Complex.sub_re, Complex.re_sum, ContinuousLinearMap.one_apply]
    simp only [g65e_re_eff]
    have := ho.sum_inner_products_le (s := Finset.univ) x
    have hx : (inner ℂ x x).re = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [hx]; linarith
  · unfold constrainedCqCodeError
    apply div_eq_zero_iff.2; left
    apply Finset.sum_eq_zero
    intro k _
    simp only
    rw [g65e_word, g65e_trace_comp, InnerProductSpace.rankOne_apply, g65e_inner_ket, g65e_ket_apply]
    simp [g65e_ket_apply]

theorem solution (E R : ℝ) (hE : 0 ≤ E) (hR : 0 ≤ R) (hRC : R < h E) :
    ∃ hP : ∀ m, constrainedCqDensity (photonSignal 0 m),
      (∀ m, photonSignal 0 m = InnerProductSpace.rankOne ℂ (constrainedCqKet m) (constrainedCqKet m)) ∧
      (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → 0 < n →
        (∃ c : constrainedCqCode (stateFamily (photonSignal 0) hP) (fun m : ℕ => (m : ℝ)) E n
          (constrainedCqMessages n R), constrainedCqCodeError c = 0) ∧
        constrainedCqError (stateFamily (photonSignal 0) hP) (fun m : ℕ => (m : ℝ)) E n
          (constrainedCqMessages n R) = 0) ∧
      reliability (stateFamily (photonSignal 0) hP) (fun m : ℕ => (m : ℝ)) E R = ⊤ := by
  refine ⟨g65e_hP, fun m => g65e_photon_eq m, ?_⟩
  obtain ⟨n0, hn0⟩ := g65e_eventually E R hE (by simpa [h] using hRC)
  have key : ∀ n : ℕ, n0 ≤ n → 0 < n →
      (∃ c : constrainedCqCode (stateFamily (photonSignal 0) g65e_hP) (fun m : ℕ => (m : ℝ)) E n
        (constrainedCqMessages n R), constrainedCqCodeError c = 0) ∧
      constrainedCqError (stateFamily (photonSignal 0) g65e_hP) (fun m : ℕ => (m : ℝ)) E n
        (constrainedCqMessages n R) = 0 := by
    intro n hn hnpos
    have hc := hn0 n hn
    set m := ⌊(n : ℝ) * E⌋₊
    set M := constrainedCqMessages n R
    have hCpos : 0 < (n + m - 1).choose m := Nat.choose_pos (by omega)
    have hMle : M ≤ (n + m - 1).choose m := by
      simp only [M, constrainedCqMessages]
      refine max_le (by omega) ?_
      have : (⌊Real.exp ((n : ℝ) * R)⌋₊ : ℝ) ≤ ((n + m - 1).choose m : ℝ) :=
        (Nat.floor_le (Real.exp_pos _).le).trans hc
      exact_mod_cast this
    have hMpos : 0 < M := by
      simp only [M, constrainedCqMessages]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
    obtain ⟨W, hW, hsum⟩ := g65e_words n m M hMle
    have hcost : ∀ k, wordCost (fun m : ℕ => (m : ℝ)) n (W k) ≤ (n : ℝ) * E := by
      intro k
      unfold wordCost
      have : (∑ i, ((W k i : ℕ) : ℝ)) = ((∑ i, W k i : ℕ) : ℝ) := by push_cast; rfl
      rw [this, hsum k]
      exact Nat.floor_le (by positivity)
    obtain ⟨c, hc0⟩ := g65e_code_exists g65e_hP E n M hMpos W hW hcost
    refine ⟨⟨c, hc0⟩, ?_⟩
    apply IsLeast.csInf_eq
    refine ⟨⟨c, hc0.symm⟩, ?_⟩
    rintro e ⟨c', rfl⟩
    exact g65e_err_nonneg g65e_hP E n M c'
  refine ⟨⟨n0, key⟩, ?_⟩
  unfold reliability
  have hev : ∀ᶠ k : ℕ in atTop,
      (if constrainedCqError (stateFamily (photonSignal 0) g65e_hP) (fun m : ℕ => (m : ℝ)) E (k + 1)
          (constrainedCqMessages (k + 1) R) = 0 then (⊤ : EReal)
        else ((-Real.log (constrainedCqError (stateFamily (photonSignal 0) g65e_hP) (fun m : ℕ => (m : ℝ)) E (k + 1)
          (constrainedCqMessages (k + 1) R)) / (k + 1 : ℕ) : ℝ) : EReal)) = ⊤ :=
    eventually_atTop.2 ⟨n0, fun k hk => if_pos (key (k + 1) (by omega) (by omega)).2⟩
  rw [limsup_congr hev, limsup_const]
