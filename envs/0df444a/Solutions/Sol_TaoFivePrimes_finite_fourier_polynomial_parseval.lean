-- Prove2me | solution 1 for TaoFivePrimes.finite_fourier_polynomial_parseval
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:35:16.893173+00:00
-- url     : https://prove2.me/submissions/1d409de3-8060-4af9-8037-3c68c58a36de

import Mathlib

set_option autoImplicit false

open MeasureTheory

lemma tao_int_fourier_8bf839f6 (n : ℤ) :
    ∫ t : AddCircle (1 : ℝ), fourier n t ∂AddCircle.haarAddCircle = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul] at h
  rw [h, Pi.single_apply]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg (Ne.symm hn), if_neg hn]

lemma tao_integrable_fourier_8bf839f6 (n : ℤ) :
    Integrable (fun t : AddCircle (1 : ℝ) => fourier n t) AddCircle.haarAddCircle :=
  (fourier n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem solution (M : Nat) (c : Nat -> Real) :
    MeasureTheory.integral AddCircle.haarAddCircle
      (fun alpha : AddCircle (1 : Real) =>
        norm (Finset.sum (Finset.range (M + 1))
          (fun k => (c k : Complex) * fourier (k : Int) alpha)) ^ 2) =
      Finset.sum (Finset.range (M + 1)) (fun k => (c k) ^ 2) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hpt : ∀ alpha : AddCircle (1 : ℝ),
      (((norm (Finset.sum (Finset.range (M + 1))
          (fun k => (c k : Complex) * fourier (k : Int) alpha)) ^ 2 : ℝ)) : ℂ) =
        ∑ k ∈ Finset.range (M + 1), ∑ l ∈ Finset.range (M + 1),
          ((c k : ℂ) * (c l : ℂ)) * fourier (-(k : ℤ) + (l : ℤ)) alpha := by
    intro alpha
    push_cast
    rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [fourier_add, fourier_neg, map_mul, Complex.conj_ofReal]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
    (tao_integrable_fourier_8bf839f6 _).const_mul _))]
  simp_rw [integral_finsetSum _ (fun l _ => (tao_integrable_fourier_8bf839f6 _).const_mul _)]
  simp_rw [integral_const_mul, tao_int_fourier_8bf839f6]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_eq_single k]
  · simp [sq]
  · intro l _ hlk
    have : -(k : ℤ) + (l : ℤ) ≠ 0 := by
      intro h
      apply hlk
      omega
    simp [this]
  · intro h
    exact absurd hk h
