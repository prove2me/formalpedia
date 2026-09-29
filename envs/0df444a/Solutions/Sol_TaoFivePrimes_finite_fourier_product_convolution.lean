-- Prove2me | solution 1 for TaoFivePrimes.finite_fourier_product_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:35:16.800992+00:00
-- url     : https://prove2.me/submissions/de8db32d-5002-4e71-a4f1-3e395755b859

import Mathlib

set_option autoImplicit false

open MeasureTheory

theorem solution (x N : Nat) (a b : Nat -> Real)
    (alpha : AddCircle (1 : Real)) :
    (Finset.sum (Finset.range (x + 1))
      (fun n => (a n : Complex) * fourier (n : Int) alpha)) *
      (Finset.sum (Finset.Icc 1 N)
        (fun j => (b j : Complex) * fourier (j : Int) alpha)) =
    Finset.sum (Finset.range (x + N + 1)) (fun k =>
      ((Finset.sum (Finset.range (x + 1)) (fun n =>
        Finset.sum (Finset.Icc 1 N) (fun j =>
          if k = n + j then a n * b j else 0)) : Real) : Complex) *
        fourier (k : Int) alpha) := by
  have hterm : ∀ k : ℕ, (((Finset.sum (Finset.range (x + 1)) (fun n =>
        Finset.sum (Finset.Icc 1 N) (fun j =>
          if k = n + j then a n * b j else 0)) : Real) : Complex) * fourier (k : Int) alpha) =
      ∑ n ∈ Finset.range (x + 1), ∑ j ∈ Finset.Icc 1 N,
        if k = n + j then (a n : ℂ) * fourier (n : ℤ) alpha * ((b j : ℂ) * fourier (j : ℤ) alpha)
        else 0 := by
    intro k
    rw [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · subst h
      push_cast
      rw [fourier_add]
      ring
    · simp
  simp_rw [hterm]
  rw [Finset.sum_comm]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_ite_eq', if_pos]
  simp only [Finset.mem_range, Finset.mem_Icc] at hn hj ⊢
  omega
