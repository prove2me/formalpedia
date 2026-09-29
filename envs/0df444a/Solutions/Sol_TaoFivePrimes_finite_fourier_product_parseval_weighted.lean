-- Prove2me | solution 1 for TaoFivePrimes.finite_fourier_product_parseval_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:39:41.768847+00:00
-- url     : https://prove2.me/submissions/7d227fec-379e-4de5-ae71-7d6b88495438

import Theorems.Thm_TaoFivePrimes_finite_fourier_polynomial_parseval
import Theorems.Thm_TaoFivePrimes_finite_fourier_product_convolution

open MeasureTheory
open TaoFivePrimes

theorem solution (x N : Nat) (a b : Nat -> Real) :
    MeasureTheory.integral AddCircle.haarAddCircle
      (fun alpha : AddCircle (1 : Real) =>
        norm ((Finset.sum (Finset.range (x + 1)) (fun n => (a n : Complex) * fourier (n : Int) alpha)) *
          (Finset.sum (Finset.Icc 1 N) (fun j => (b j : Complex) * fourier (j : Int) alpha))) ^ 2) =
      Finset.sum (Finset.range (x + N + 1)) (fun k =>
        (Finset.sum (Finset.range (x + 1)) (fun n =>
          Finset.sum (Finset.Icc 1 N) (fun j =>
            if k = n + j then a n * b j else 0))) ^ 2) := by
  let c : Nat -> Real := fun k =>
    Finset.sum (Finset.range (x + 1)) (fun n =>
      Finset.sum (Finset.Icc 1 N) (fun j => if k = n + j then a n * b j else 0))
  have hconv (alpha : AddCircle (1 : Real)) :=
    TaoFivePrimes.finite_fourier_product_convolution x N a b alpha
  simp_rw [hconv]
  simpa [c] using TaoFivePrimes.finite_fourier_polynomial_parseval (x + N) c
