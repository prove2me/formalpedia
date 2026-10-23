-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P14.splitFockStatistics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:07:19.986333+00:00
-- url     : https://prove2.me/submissions/73bc04b1-aa0f-4610-8437-eae318d1b07f

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
noncomputable section
open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet fockOutput)

lemma x8_ket_apply (m n : ℕ) (pq : ℕ × ℕ) :
    (fockKet m n : Fock) pq = if pq = (m, n) then 1 else 0 := by
  unfold fockKet
  rw [lp.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all [Pi.single_apply]

lemma x8_coef_id (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℂ) * (Real.sqrt (((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ)) /
        (Nat.factorial n : ℝ)) : ℂ) = (Real.sqrt (n.choose k : ℝ) : ℂ) := by
  have hc : (n.choose k : ℝ) * ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ)) =
      (Nat.factorial n : ℝ) := by
    rw [← mul_assoc]; exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hpos : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have hf : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
  congr 1
  rw [show ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ)) / (Nat.factorial n : ℝ)
      = 1 / (n.choose k : ℝ) by rw [← hc]; field_simp]
  rw [Real.sqrt_div' _ hpos.le, Real.sqrt_one]
  have hs : 0 < Real.sqrt (n.choose k : ℝ) := Real.sqrt_pos.2 hpos
  field_simp
  rw [Real.sq_sqrt hpos.le]

lemma x8_out_eq (B : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    fockOutput B n 0 =
      ∑ k ∈ Finset.range (n + 1),
        ((Real.sqrt (n.choose k : ℝ) : ℂ) * B 0 0 ^ k * B 1 0 ^ (n - k)) •
          fockKet k (n - k) := by
  unfold fockOutput
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right,
    Nat.cast_one, mul_one, Nat.sub_self, add_zero, Nat.factorial_zero, pow_zero]
  congr 1
  rw [← x8_coef_id n k hk']

def x8c (B : Matrix (Fin 2) (Fin 2) ℂ) (n k : ℕ) : ℂ :=
  (Real.sqrt (n.choose k : ℝ) : ℂ) * B 0 0 ^ k * B 1 0 ^ (n - k)

lemma x8_sum_apply (B : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (pq : ℕ × ℕ) :
    (∑ k ∈ Finset.range (n + 1), x8c B n k • (fockKet k (n - k) : Fock)) pq =
      if pq.1 + pq.2 = n then x8c B n pq.1 else 0 := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, x8_ket_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  obtain ⟨p, q⟩ := pq
  simp only [Prod.mk.injEq]
  split_ifs with h
  · rw [Finset.sum_eq_single p]
    · simp; omega
    · intro b _ hb; simp [Ne.symm hb]
    · intro hp; exfalso; simp at hp; omega
  · refine Finset.sum_eq_zero fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [if_neg]; omega

lemma x8_out_apply (B : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (pq : ℕ × ℕ) :
    (fockOutput B n 0 : Fock) pq = if pq.1 + pq.2 = n then x8c B n pq.1 else 0 := by
  rw [x8_out_eq]; exact x8_sum_apply B n pq

lemma x8_pc (B : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    passiveCoefficients B (fockKet n 0) = ⇑(fockOutput B n 0 : Fock) := by
  funext pq
  unfold passiveCoefficients
  have : ∀ m ∈ Finset.range (pq.1 + pq.2 + 1),
      (fockKet n 0 : Fock) (m, pq.1 + pq.2 - m) * (occupationOutput B m (pq.1 + pq.2 - m)) pq =
      if m = n then (if pq.1 + pq.2 = n then (fockOutput B n 0 : Fock) pq else 0) else 0 := by
    intro m hm
    have := Finset.mem_range.1 hm
    rw [x8_ket_apply]
    simp only [Prod.mk.injEq]
    by_cases h1 : m = n
    · subst h1
      by_cases h2 : pq.1 + pq.2 = m
      · simp [h2]
      · rw [if_neg (by omega), if_pos rfl, if_neg h2]; simp
    · rw [if_neg (by tauto), if_neg h1]; simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  split_ifs with h1 h2
  · rfl
  · rw [x8_out_apply, if_neg h2]
  · simp at h1; rw [x8_out_apply, if_neg (by omega)]

lemma x8_pa (B : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    passiveApply B (fockKet n 0) = fockOutput B n 0 := by
  have hm : Memℓp (passiveCoefficients B (fockKet n 0)) 2 := by
    rw [x8_pc]; exact (fockOutput B n 0).2
  unfold passiveApply
  rw [dif_pos hm]
  ext pq
  simp [x8_pc]

lemma x8_f_apply (B : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (pq : ℕ × ℕ) :
    passiveApply B (fockKet n 0) pq = if pq.1 + pq.2 = n then x8c B n pq.1 else 0 := by
  rw [x8_pa, x8_out_apply]

lemma x8_c_nsq (B : Matrix (Fin 2) (Fin 2) ℂ) (n k : ℕ) :
    Complex.normSq (x8c B n k) =
      (n.choose k : ℝ) * Complex.normSq (B 0 0) ^ k * Complex.normSq (B 1 0) ^ (n - k) := by
  unfold x8c
  simp only [map_mul, map_pow, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (by positivity)]

lemma x8_col (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    Complex.normSq (B 0 0) + Complex.normSq (B 1 0) = 1 := by
  rw [Matrix.mem_unitaryGroup_iff'] at hB
  have h := congrFun (congrFun hB 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at h
  have : ((Complex.normSq (B 0 0) + Complex.normSq (B 1 0) : ℝ) : ℂ) = 1 := by
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    exact h
  exact_mod_cast this

lemma x8_supp (B : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    ∀ pq ∉ Finset.HasAntidiagonal.antidiagonal n, Complex.normSq (passiveApply B (fockKet n 0) pq) = 0 := by
  intro pq hpq
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
  rw [x8_f_apply, if_neg hpq, map_zero]

lemma x8_tsum (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) (n : ℕ) :
    (∑' mn : ℕ × ℕ, Complex.normSq (passiveApply B (fockKet n 0) mn)) = 1 := by
  rw [tsum_eq_sum (s := Finset.HasAntidiagonal.antidiagonal n) (x8_supp B n),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have : ∀ k ∈ Finset.range (n + 1),
      Complex.normSq (passiveApply B (fockKet n 0) (k, n - k)) =
      Complex.normSq (B 0 0) ^ k * Complex.normSq (B 1 0) ^ (n - k) * (n.choose k : ℝ) := by
    intro k hk
    have := Finset.mem_range.1 hk
    rw [x8_f_apply, if_pos (by simp; omega), x8_c_nsq]; ring
  rw [Finset.sum_congr rfl this, ← add_pow, x8_col B hB, one_pow]

theorem x8_main (B : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) (n : ℕ) :
    passiveApply B (fockKet n 0) =
      ∑ k ∈ Finset.range (n + 1),
        ((Real.sqrt (n.choose k : ℝ) : ℂ) * B 0 0 ^ k * B 1 0 ^ (n - k)) •
          fockKet k (n - k) ∧
    ‖passiveApply B (fockKet n 0)‖ = 1 ∧
    (∀ n1 n2 : ℕ, Complex.normSq (passiveApply B (fockKet n 0) (n1, n2)) =
      if n1 + n2 = n then
        (n.choose n1 : ℝ) * Complex.normSq (B 0 0) ^ n1 *
          (1 - Complex.normSq (B 0 0)) ^ n2 else 0) ∧
    Summable (fun mn : ℕ × ℕ => Complex.normSq (passiveApply B (fockKet n 0) mn)) ∧
    (∑' mn : ℕ × ℕ, Complex.normSq (passiveApply B (fockKet n 0) mn)) = 1 := by
  refine ⟨by rw [x8_pa, x8_out_eq], ?_, ?_, summable_of_ne_finset_zero (x8_supp B n),
    x8_tsum B hB n⟩
  · have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) (passiveApply B (fockKet n 0))
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    have h2 : ∀ mn, ‖(passiveApply B (fockKet n 0) : Fock) mn‖ ^ 2 =
        Complex.normSq (passiveApply B (fockKet n 0) mn) := fun mn =>
      (Complex.normSq_eq_norm_sq _).symm
    simp only [h2, x8_tsum B hB n] at h
    have h0 := norm_nonneg (passiveApply B (fockKet n 0))
    nlinarith
  · intro n1 n2
    rw [x8_f_apply]
    split_ifs with h
    · rw [x8_c_nsq, show n - n1 = n2 by simp at h; omega,
        show 1 - Complex.normSq (B 0 0) = Complex.normSq (B 1 0) by linarith [x8_col B hB]]
    · exact map_zero _

end QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Frontier18.P14 in
open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet) in
theorem solution (B : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) (n : ℕ) :
    passiveApply B (fockKet n 0) =
      ∑ k ∈ Finset.range (n + 1),
        ((Real.sqrt (n.choose k : ℝ) : ℂ) * B 0 0 ^ k * B 1 0 ^ (n - k)) •
          fockKet k (n - k) ∧
    ‖passiveApply B (fockKet n 0)‖ = 1 ∧
    (∀ n1 n2 : ℕ, Complex.normSq (passiveApply B (fockKet n 0) (n1, n2)) =
      if n1 + n2 = n then
        (n.choose n1 : ℝ) * Complex.normSq (B 0 0) ^ n1 *
          (1 - Complex.normSq (B 0 0)) ^ n2 else 0) ∧
    Summable (fun mn : ℕ × ℕ => Complex.normSq (passiveApply B (fockKet n 0) mn)) ∧
    (∑' mn : ℕ × ℕ, Complex.normSq (passiveApply B (fockKet n 0) mn)) = 1 :=
  x8_main B hB n
