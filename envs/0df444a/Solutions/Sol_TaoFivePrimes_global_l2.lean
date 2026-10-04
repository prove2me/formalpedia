-- Prove2me | solution 1 for TaoFivePrimes.global_l2
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T01:57:08.847178+00:00
-- url     : https://prove2.me/submissions/e4a78634-82df-4e08-9987-41666687ddd4

import Definitions.Def_TaoFivePrimes_SmoothedSum
import Theorems.Thm_MeasureTheory_integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq

open MeasureTheory
open scoped ComplexConjugate BigOperators ArithmeticFunction.vonMangoldt

namespace TaoGlobalL2Proof

/-- Finite Parseval for naturally indexed Fourier modes on the unit circle. -/
theorem finite_parseval (s : Finset ℕ) (a : ℕ → ℝ) :
    Integrable (fun α : AddCircle (1 : ℝ) ↦
      ‖∑ n ∈ s, (a n : ℂ) * fourier (n : ℤ) α‖ ^ 2) AddCircle.haarAddCircle ∧
    (∫ α : AddCircle (1 : ℝ), ‖∑ n ∈ s, (a n : ℂ) * fourier (n : ℤ) α‖ ^ 2
      ∂AddCircle.haarAddCircle) = ∑ n ∈ s, (a n) ^ 2 := by
  classical
  let φ : s → AddCircle (1 : ℝ) → ℂ := fun j ↦ fourier (-((j : ℕ) : ℤ))
  have hφ : ∀ j, MemLp (φ j) 2 AddCircle.haarAddCircle := by
    intro j
    exact ContinuousMap.memLp (μ := AddCircle.haarAddCircle) (p := 2) ℂ
      (fourier (-((j : ℕ) : ℤ)))
  have horth : ∀ j j' : s,
      (∫ α : AddCircle (1 : ℝ), φ j α * conj (φ j' α) ∂AddCircle.haarAddCircle) =
        if j = j' then (1 : ℂ) else 0 := by
    intro j j'
    rw [← ContinuousMap.inner_toLp AddCircle.haarAddCircle
      (fourier (-((j' : ℕ) : ℤ))) (fourier (-((j : ℕ) : ℤ)))]
    change inner ℂ (fourierLp 2 (-((j' : ℕ) : ℤ)))
      (fourierLp 2 (-((j : ℕ) : ℤ))) = _
    rw [orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))]
    by_cases hj : j = j'
    · subst j'
      simp only [ite_true]
    · have hne : -((j' : ℕ) : ℤ) ≠ -((j : ℕ) : ℤ) := by
        intro he
        apply hj
        apply Subtype.ext
        exact Int.ofNat_inj.mp (neg_inj.mp he).symm
      simp only [hne, hj, ite_false]
  have h := MeasureTheory.integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq
    AddCircle.haarAddCircle φ hφ (fun j : s ↦ (a j : ℂ)) (fun _ ↦ 1) horth
  have hsum (α : AddCircle (1 : ℝ)) :
      (∑ j : s, conj (φ j α) • (a j : ℂ)) =
        ∑ n ∈ s, (a n : ℂ) * fourier (n : ℤ) α := by
    simp only [φ, fourier_neg, Complex.conj_conj, smul_eq_mul]
    rw [← Finset.sum_coe_sort s (fun n ↦ (a n : ℂ) * fourier (n : ℤ) α)]
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  have hcoeff : (∑ j : s, (1 : ℝ) * ‖(a j : ℂ)‖ ^ 2) = ∑ n ∈ s, (a n) ^ 2 := by
    simp only [one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact Finset.sum_coe_sort s (fun n ↦ (a n) ^ 2)
  simpa only [hsum, hcoeff] using h

end TaoGlobalL2Proof

namespace TaoGlobalL2Proof

open TaoFivePrimes

theorem smoothedSum_eq_sum {η : ℝ → ℝ} {q : ℕ} {x : ℝ}
    (hx : 1 ≤ x) (hη : ∀ t : ℝ, 1 < t → η t = 0) (α : AddCircle (1 : ℝ)) :
    smoothedSum η q x α =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        if n.Coprime q then
          (η ((n : ℝ) / x) * Λ n : ℝ) • fourier (n : ℤ) α else 0 := by
  unfold smoothedSum
  apply tsum_eq_sum
  intro n hn
  have hnx : x < (n : ℝ) := by
    apply lt_of_not_ge
    intro h
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor h)))
  have harg : 1 < (n : ℝ) / x :=
    (lt_div_iff₀ (lt_of_lt_of_le zero_lt_one hx)).2 (by simpa using hnx)
  simp [hη _ harg]

theorem smoothedSum_zero_eq_sum {η : ℝ → ℝ} {q : ℕ} {x : ℝ}
    (hx : 1 ≤ x) (hη : ∀ t : ℝ, 1 < t → η t = 0) :
    smoothedSum η q x 0 =
      ((∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        if n.Coprime q then η ((n : ℝ) / x) * Λ n else 0 : ℝ) : ℂ) := by
  rw [smoothedSum_eq_sum hx hη, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : n.Coprime q
  · rw [if_pos hc, if_pos hc]
    simp only [fourier_eval_zero, Complex.real_smul, mul_one]
  · rw [if_neg hc, if_neg hc]
    rfl

theorem smoothedSum_sq_zero_re {η : ℝ → ℝ} {q : ℕ} {x : ℝ}
    (hx : 1 ≤ x) (hη : ∀ t : ℝ, 1 < t → η t = 0) :
    (smoothedSum (fun t ↦ (η t) ^ 2) q x 0).re =
      ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun n ↦ n.Coprime q),
        (η ((n : ℝ) / x)) ^ 2 * Λ n := by
  have hηsq : ∀ t : ℝ, 1 < t → (η t) ^ 2 = 0 := by
    intro t ht
    simp [hη t ht]
  simpa only [Complex.ofReal_re, Finset.sum_filter] using
    congrArg Complex.re (smoothedSum_zero_eq_sum (q := q) hx hηsq)

end TaoGlobalL2Proof

open MeasureTheory TaoFivePrimes TaoGlobalL2Proof

/-- Tao's global L² estimate, with explicit integrability and only the upper support hypothesis. -/
theorem solution (η : ℝ → ℝ) (q : ℕ) (x : ℝ)
    (hx : 1 ≤ x) (hη : ∀ t : ℝ, 1 < t → η t = 0) :
    Integrable (fun α : AddCircle (1 : ℝ) ↦ ‖smoothedSum η q x α‖ ^ 2)
      AddCircle.haarAddCircle ∧
    (∫ α : AddCircle (1 : ℝ), ‖smoothedSum η q x α‖ ^ 2 ∂AddCircle.haarAddCircle) ≤
      (smoothedSum (fun t ↦ (η t) ^ 2) q x 0).re * Real.log x := by
  classical
  let s := (Finset.range (⌊x⌋₊ + 1)).filter (fun n ↦ n.Coprime q)
  have hS : ∀ α : AddCircle (1 : ℝ), smoothedSum η q x α =
      ∑ n ∈ s, ((η ((n : ℝ) / x) * Λ n : ℝ) : ℂ) * fourier (n : ℤ) α := by
    intro α
    rw [smoothedSum_eq_sum hx hη, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime q <;> simp [hc, Complex.real_smul]
  have hP := finite_parseval s (fun n ↦ η ((n : ℝ) / x) * Λ n)
  simp_rw [← hS] at hP
  refine ⟨hP.1, hP.2.le.trans ?_⟩
  rw [smoothedSum_sq_zero_re hx hη, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  have hnf : n ≤ ⌊x⌋₊ := Nat.le_of_lt_succ
    (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
  have hnx : (n : ℝ) ≤ x :=
    (Nat.cast_le.mpr hnf).trans (Nat.floor_le (le_trans zero_le_one hx))
  have hlog : Λ n ≤ Real.log x := by
    by_cases hn0 : n = 0
    · subst n
      simpa using Real.log_nonneg hx
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)) hnx)
  have hΛ : (Λ n) ^ 2 ≤ Λ n * Real.log x := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left hlog ArithmeticFunction.vonMangoldt_nonneg
  calc
    (η ((n : ℝ) / x) * Λ n) ^ 2 = (η ((n : ℝ) / x)) ^ 2 * (Λ n) ^ 2 := mul_pow _ _ _
    _ ≤ (η ((n : ℝ) / x)) ^ 2 * (Λ n * Real.log x) :=
      mul_le_mul_of_nonneg_left hΛ (sq_nonneg _)
    _ = (η ((n : ℝ) / x)) ^ 2 * Λ n * Real.log x := (mul_assoc _ _ _).symm
