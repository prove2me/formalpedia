-- Prove2me | solution 1 for binomial_incomplete_beta_at_mean_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T15:01:48.781289+00:00
-- url     : https://prove2.me/submissions/febf4a5d-9501-49e3-a6e9-3b07f289da49

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_matrix_completion_fixed_cardinality
import Theorems.Thm_binomial_upper_tail_eq_incomplete_beta
import Theorems.Thm_binomial_integer_mean_upper_tail_le_half

open scoped BigOperators
open Finset
open MatrixCompletion

/-- Reduction of the incomplete-beta-at-mean bound to the binomial median.

The integral `∫_0^{m/N} N·C(N-1,m)·t^m·(1-t)^{N-1-m} dt` is the regularized
incomplete beta `I_{m/N}(m+1, N-m)`, which by the incomplete-beta ↔ binomial-tail
identity (Abramowitz–Stegun 26.5.24; Feller, *An Introduction to Probability
Theory*, Vol. 2, §7.2 — order statistics of uniforms) equals the strict upper
binomial tail `∑_{k=m+1}^{N} C(N,k)(m/N)^k(1-m/N)^{N-k}`.  That identity is the
already-proved child `binomial_upper_tail_eq_incomplete_beta` specialized to
`p = m/N`.  The tail is then `≤ 1/2` by the integer-mean binomial median
(`binomial_integer_mean_upper_tail_le_half`). -/
theorem solution (N m : ℕ) (h : m < N) :
    (∫ t in (0:ℝ)..((m : ℝ) / (N : ℝ)),
        (N : ℝ) * (Nat.choose (N-1) m : ℝ) * t ^ m * (1 - t) ^ (N - 1 - m)) ≤ (1 / 2 : ℝ) := by
  rw [← binomial_upper_tail_eq_incomplete_beta N m h ((m : ℝ) / (N : ℝ))]
  exact binomial_integer_mean_upper_tail_le_half N m h
