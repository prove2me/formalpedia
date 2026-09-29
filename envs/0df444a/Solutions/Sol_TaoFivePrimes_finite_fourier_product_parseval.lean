-- Prove2me | solution 1 for TaoFivePrimes.finite_fourier_product_parseval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:13:02.877729+00:00
-- url     : https://prove2.me/submissions/dc8f0447-be0c-4e30-ac25-552880a34193

import Theorems.Thm_TaoFivePrimes_finite_fourier_product_parseval_weighted
open TaoFivePrimes

theorem solution (x N : Nat) (a : Nat -> Real) :
    MeasureTheory.integral AddCircle.haarAddCircle
      (fun alpha : AddCircle (1 : Real) =>
        norm ((Finset.sum (Finset.range (x + 1)) (fun n => (a n : Complex) * fourier (n : Int) alpha)) *
          (Finset.sum (Finset.Icc 1 N) (fun j => (1 : Complex) * fourier (j : Int) alpha))) ^ 2) =
      Finset.sum (Finset.range (x + N + 1)) (fun k =>
        (Finset.sum (Finset.range (x + 1)) (fun n =>
          Finset.sum (Finset.Icc 1 N) (fun j =>
            if k = n + j then a n else 0))) ^ 2) := by
  simpa using
    TaoFivePrimes.finite_fourier_product_parseval_weighted x N a (fun _ => (1 : Real))
