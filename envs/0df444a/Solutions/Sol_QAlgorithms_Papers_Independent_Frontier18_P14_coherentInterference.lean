-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P14.coherentInterference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:15:11.455997+00:00
-- url     : https://prove2.me/submissions/e9810491-1a32-4945-bd15-abf1cc0dd6fe

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
noncomputable section
open scoped Matrix ComplexConjugate Nat

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet fockOutput)

lemma x8_w (a : ℂ) (n : ℕ) : Complex.normSq (coherentCoefficient a n) =
    Real.exp (-Complex.normSq a) * (Complex.normSq a ^ n / n !) := by
  unfold coherentCoefficient
  simp only [map_div₀, map_mul, map_pow, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (by positivity), ← Real.exp_add]
  ring_nf

lemma x8_w_summable (a : ℂ) : Summable (fun n : ℕ => Complex.normSq (coherentCoefficient a n)) := by
  simp only [x8_w]; exact (Real.summable_pow_div_factorial _).mul_left _

lemma x8_exp_tsum (x : ℝ) : ∑' n : ℕ, x ^ n / n ! = Real.exp x := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

lemma x8_w_tsum (a : ℂ) : ∑' n : ℕ, Complex.normSq (coherentCoefficient a n) = 1 := by
  simp only [x8_w]
  rw [tsum_mul_left, x8_exp_tsum, ← Real.exp_add, neg_add_cancel, Real.exp_zero]

lemma x8_pair_summable (a b : ℂ) :
    Summable (fun mn : ℕ × ℕ => Complex.normSq (coherentPairCoefficients a b mn)) := by
  simp only [coherentPairCoefficients, map_mul]
  exact (x8_w_summable a).mul_of_nonneg (x8_w_summable b) (fun _ => Complex.normSq_nonneg _)
    (fun _ => Complex.normSq_nonneg _)

lemma x8_pair_tsum (a b : ℂ) :
    ∑' mn : ℕ × ℕ, Complex.normSq (coherentPairCoefficients a b mn) = 1 := by
  simp only [coherentPairCoefficients, map_mul]
  rw [← (x8_w_summable a).tsum_mul_tsum (x8_w_summable b), x8_w_tsum, x8_w_tsum, one_mul]
  have := x8_pair_summable a b
  simpa [coherentPairCoefficients] using this

lemma x8_memlp_iff (f : ℕ × ℕ → ℂ) :
    Memℓp f 2 ↔ Summable (fun mn => Complex.normSq (f mn)) := by
  rw [memℓp_gen_iff (by norm_num)]
  simp [Complex.normSq_eq_norm_sq]

lemma x8_pair_mem (a b : ℂ) : Memℓp (coherentPairCoefficients a b) 2 :=
  (x8_memlp_iff _).2 (x8_pair_summable a b)

lemma x8_pair_apply (a b : ℂ) (mn : ℕ × ℕ) :
    coherentPair a b mn = coherentPairCoefficients a b mn := by
  unfold coherentPair; rw [dif_pos (x8_pair_mem a b)]

lemma x8_norm_eq (psi : Fock) (h : ∑' mn, Complex.normSq (psi mn) = 1) : ‖psi‖ = 1 := by
  have h1 := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) psi
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1
  simp only [← Complex.normSq_eq_norm_sq, h] at h1
  have h0 := norm_nonneg psi
  nlinarith

lemma x8_pair_norm (a b : ℂ) : ‖coherentPair a b‖ = 1 :=
  x8_norm_eq _ (by simp only [x8_pair_apply]; exact x8_pair_tsum a b)

open Polynomial in
lemma x8_lin_pow (c d : ℂ) (m : ℕ) : (C c * X + C d) ^ m =
    ∑ k ∈ Finset.range (m + 1), C ((m.choose k : ℂ) * c ^ k * d ^ (m - k)) * X ^ k := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mul_pow, map_mul, map_pow, map_natCast]
  ring

open Polynomial in
lemma x8_coeff_PQ (B : Matrix (Fin 2) (Fin 2) ℂ) (m n p : ℕ) :
    ((C (B 0 0) * X + C (B 1 0)) ^ m * (C (B 0 1) * X + C (B 1 1)) ^ n).coeff p =
      ∑ k ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (n + 1),
        if k + l = p then ((m.choose k : ℂ) * B 0 0 ^ k * B 1 0 ^ (m - k)) *
          ((n.choose l : ℂ) * B 0 1 ^ l * B 1 1 ^ (n - l)) else 0 := by
  rw [x8_lin_pow, x8_lin_pow, Finset.sum_mul_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [finsetSum_coeff]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show ∀ x y : ℂ, C x * X ^ k * (C y * X ^ l) = C (x * y) * X ^ (k + l) by
    intro x y; rw [map_mul, pow_add]; ring, coeff_C_mul_X_pow]
  split_ifs with h1 h2 h2 <;> first | rfl | omega

lemma x8_fo_apply (B : Matrix (Fin 2) (Fin 2) ℂ) (m n : ℕ) (pq : ℕ × ℕ) :
    (fockOutput B m n : Fock) pq =
      ∑ k ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (n + 1),
        ((m.choose k : ℂ) * (n.choose l : ℂ) *
          (Real.sqrt (((Nat.factorial (k + l) : ℝ) *
            (Nat.factorial (m - k + (n - l)) : ℝ)) /
            ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
          B 0 0 ^ k * B 1 0 ^ (m - k) * B 0 1 ^ l * B 1 1 ^ (n - l)) *
        (if pq = (k + l, m - k + (n - l)) then 1 else 0) := by
  unfold fockOutput
  rw [lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  unfold fockKet
  rw [lp.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all [Pi.single_apply]

open Polynomial in
lemma x8_fo_eq (B : Matrix (Fin 2) (Fin 2) ℂ) (m n p q : ℕ) (hpq : p + q = m + n) :
    (fockOutput B m n : Fock) (p, q) =
      (Real.sqrt (((Nat.factorial p : ℝ) * (Nat.factorial q : ℝ)) /
            ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
      ((C (B 0 0) * X + C (B 1 0)) ^ m * (C (B 0 1) * X + C (B 1 1)) ^ n).coeff p := by
  rw [x8_fo_apply, x8_coeff_PQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hk' := Finset.mem_range.1 hk
  have hl' := Finset.mem_range.1 hl
  by_cases h : k + l = p
  · rw [if_pos h, if_pos (by rw [Prod.mk.injEq]; omega)]
    have h2 : m - k + (n - l) = q := by omega
    rw [h, h2]; ring
  · rw [if_neg h, if_neg (by rw [Prod.mk.injEq]; omega)]; ring

abbrev x8s (n : ℕ) : ℂ := (Real.sqrt (n ! : ℝ) : ℂ)

lemma x8s_sq (n : ℕ) : x8s n ^ 2 = (n ! : ℂ) := by
  unfold x8s
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl

lemma x8s_ne (n : ℕ) : x8s n ≠ 0 := by
  unfold x8s
  rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos n)).ne'

lemma x8_sqrt4 (p q m n : ℕ) :
    (Real.sqrt (((p ! : ℝ) * (q ! : ℝ)) / ((m ! : ℝ) * (n ! : ℝ))) : ℂ) =
      x8s p * x8s q / (x8s m * x8s n) := by
  unfold x8s
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by positivity)]
  push_cast; rfl

open Polynomial in
lemma x8_coeff_lin (c d : ℂ) (N p : ℕ) (hp : p ≤ N) :
    ((C c * X + C d) ^ N).coeff p = (N.choose p : ℂ) * c ^ p * d ^ (N - p) := by
  rw [x8_lin_pow, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.2 (by omega))]

lemma x8_cc_apply (a b : ℂ) (m n : ℕ) :
    coherentPair a b (m, n) =
      (Real.exp (-Complex.normSq a / 2) : ℂ) * (Real.exp (-Complex.normSq b / 2) : ℂ) *
        a ^ m * b ^ n / (x8s m * x8s n) := by
  rw [x8_pair_apply]
  unfold coherentPairCoefficients coherentCoefficient
  have := x8s_ne m; have := x8s_ne n
  field_simp

open Polynomial in
lemma x8_pc_coh (B : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) (p q : ℕ) :
    passiveCoefficients B (coherentPair a b) (p, q) =
      (Real.exp (-Complex.normSq a / 2) : ℂ) * (Real.exp (-Complex.normSq b / 2) : ℂ) *
        (B 0 0 * a + B 0 1 * b) ^ p * (B 1 0 * a + B 1 1 * b) ^ q / (x8s p * x8s q) := by
  unfold passiveCoefficients
  simp only
  set N := p + q with hN
  set Ea : ℂ := (Real.exp (-Complex.normSq a / 2) : ℂ)
  set Eb : ℂ := (Real.exp (-Complex.normSq b / 2) : ℂ)
  set K : ℂ := Ea * Eb * x8s p * x8s q / (N ! : ℂ)
  have hNf : (N ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  have hterm : ∀ m ∈ Finset.range (N + 1),
      coherentPair a b (m, N - m) * (occupationOutput B m (N - m) : Fock) (p, q) =
      K * (C ((N.choose m : ℂ) * a ^ m * b ^ (N - m)) *
        ((C (B 0 0) * X + C (B 1 0)) ^ m * (C (B 0 1) * X + C (B 1 1)) ^ (N - m))).coeff p := by
    intro m hm
    have hm' : m ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    rw [x8_cc_apply, x8_fo_eq B m (N - m) p q (by omega), coeff_C_mul, x8_sqrt4]
    have hc : (N.choose m : ℂ) * (m ! : ℂ) * ((N - m) ! : ℂ) = (N ! : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hm'
    have h1 := x8s_sq m; have h2 := x8s_sq (N - m)
    have := x8s_ne m; have := x8s_ne (N - m)
    have hch : (N.choose m : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm').ne'
    simp only [K, Ea, Eb]
    rw [← hc, ← h1, ← h2]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← finsetSum_coeff]
  have hsum : ∑ m ∈ Finset.range (N + 1), C ((N.choose m : ℂ) * a ^ m * b ^ (N - m)) *
        ((C (B 0 0) * X + C (B 1 0)) ^ m * (C (B 0 1) * X + C (B 1 1)) ^ (N - m)) =
      (C (B 0 0 * a + B 0 1 * b) * X + C (B 1 0 * a + B 1 1 * b)) ^ N := by
    rw [show C (B 0 0 * a + B 0 1 * b) * X + C (B 1 0 * a + B 1 1 * b) =
        C a * (C (B 0 0) * X + C (B 1 0)) + C b * (C (B 0 1) * X + C (B 1 1)) by
      simp only [map_add, map_mul]; ring, add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [map_mul, map_pow, map_natCast, mul_pow]
    ring
  rw [hsum, x8_coeff_lin _ _ _ _ (by omega), show N - p = q by omega]
  have hc : (N.choose p : ℂ) * (p ! : ℂ) * (q ! : ℂ) = (N ! : ℂ) := by
    have := Nat.choose_mul_factorial_mul_factorial (show p ≤ N by omega)
    rw [show N - p = q by omega] at this
    exact_mod_cast this
  have h1 := x8s_sq p; have h2 := x8s_sq q
  have := x8s_ne p; have := x8s_ne q
  have hch : (N.choose p : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (show p ≤ N by omega)).ne'
  simp only [K]
  rw [← hc, ← h1, ← h2]
  field_simp

lemma x8_gauss (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) (a b : ℂ) :
    Complex.normSq (B 0 0 * a + B 0 1 * b) + Complex.normSq (B 1 0 * a + B 1 1 * b) =
      Complex.normSq a + Complex.normSq b := by
  rw [Matrix.mem_unitaryGroup_iff'] at hB
  have e : ∀ i j, (star B * B) i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j => by rw [hB]
  have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at e00 e01 e10 e11
  have : ((Complex.normSq (B 0 0 * a + B 0 1 * b) + Complex.normSq (B 1 0 * a + B 1 1 * b) : ℝ) : ℂ)
      = ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) := by
    push_cast
    simp only [Complex.normSq_eq_conj_mul_self, map_add, map_mul]
    linear_combination (conj a * a) * e00 + (conj b * b) * e11 + (conj a * b) * e01 +
      (conj b * a) * e10
  exact_mod_cast this

lemma x8_part2 (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) (a b : ℂ) :
    passiveApply B (coherentPair a b) =
      coherentPair (B 0 0 * a + B 0 1 * b) (B 1 0 * a + B 1 1 * b) := by
  have hE : (Real.exp (-Complex.normSq a / 2) : ℂ) * (Real.exp (-Complex.normSq b / 2) : ℂ) =
      (Real.exp (-Complex.normSq (B 0 0 * a + B 0 1 * b) / 2) : ℂ) *
        (Real.exp (-Complex.normSq (B 1 0 * a + B 1 1 * b) / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    congr 2
    linarith [x8_gauss B hB a b]
  have hf : passiveCoefficients B (coherentPair a b) =
      ⇑(coherentPair (B 0 0 * a + B 0 1 * b) (B 1 0 * a + B 1 1 * b)) := by
    funext pq
    obtain ⟨p, q⟩ := pq
    rw [x8_pc_coh, x8_cc_apply, hE]
  have hm : Memℓp (passiveCoefficients B (coherentPair a b)) 2 := by
    rw [hf]; exact (coherentPair _ _).2
  unfold passiveApply
  rw [dif_pos hm]
  ext pq
  simp [hf]

lemma x8_balanced_unitary : balanced ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have h2' : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [sq, h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balanced, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.conj_ofReal] <;>
    field_simp <;> (try simp only [h2']) <;> ring

theorem x8_main :
    (∀ a b : ℂ, Memℓp (coherentPairCoefficients a b) 2 ∧
      ‖coherentPair a b‖ = 1 ∧
      ∀ mn, coherentPair a b mn = coherentCoefficient a mn.1 * coherentCoefficient b mn.2) ∧
    (∀ (B : Matrix (Fin 2) (Fin 2) ℂ),
      B ∈ Matrix.unitaryGroup (Fin 2) ℂ → ∀ a b : ℂ,
      passiveApply B (coherentPair a b) =
        coherentPair (B 0 0 * a + B 0 1 * b) (B 1 0 * a + B 1 1 * b)) ∧
    (∀ a : ℂ,
      passiveApply balanced (coherentPair a a) = coherentPair ((Real.sqrt 2 : ℂ) * a) 0 ∧
      passiveApply balanced (coherentPair a (-a)) = coherentPair 0 (-(Real.sqrt 2 : ℂ) * a)) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  refine ⟨fun a b => ⟨x8_pair_mem a b, x8_pair_norm a b, fun mn => x8_pair_apply a b mn⟩,
    x8_part2, fun a => ⟨?_, ?_⟩⟩
  · rw [x8_part2 _ x8_balanced_unitary]
    congr 1 <;> simp [balanced] <;> field_simp <;> linear_combination (-a) * h2
  · rw [x8_part2 _ x8_balanced_unitary]
    congr 1 <;> simp [balanced] <;> field_simp <;> linear_combination a * h2

end QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Frontier18.P14 in
theorem solution :
    (∀ a b : ℂ, Memℓp (coherentPairCoefficients a b) 2 ∧
      ‖coherentPair a b‖ = 1 ∧
      ∀ mn, coherentPair a b mn = coherentCoefficient a mn.1 * coherentCoefficient b mn.2) ∧
    (∀ (B : Matrix (Fin 2) (Fin 2) ℂ),
      B ∈ Matrix.unitaryGroup (Fin 2) ℂ → ∀ a b : ℂ,
      passiveApply B (coherentPair a b) =
        coherentPair (B 0 0 * a + B 0 1 * b) (B 1 0 * a + B 1 1 * b)) ∧
    (∀ a : ℂ,
      passiveApply balanced (coherentPair a a) = coherentPair ((Real.sqrt 2 : ℂ) * a) 0 ∧
      passiveApply balanced (coherentPair a (-a)) = coherentPair 0 (-(Real.sqrt 2 : ℂ) * a)) :=
  x8_main
