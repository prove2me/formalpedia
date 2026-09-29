-- Prove2me | solution 1 for TaoFivePrimes.vaughan_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T19:35:49.935091+00:00
-- url     : https://prove2.me/submissions/2431b8a6-2b88-4648-a470-d6b8910e3ba4

import Mathlib
import Definitions.Def_TaoFivePrimes_VaughanTruncation
import Theorems.Thm_TaoFivePrimes_vaughan_identity
import Theorems.Thm_TaoFivePrimes_sum_dirichlet_pairing
open ArithmeticFunction Finset TaoFivePrimes

/-- **Vaughan's identity paired with a test function** (Tao, Lemma 4.11, the displayed
decomposition in its proof).  For `F` supported in `(V, N)`, the prime sum splits into two
linear (Type I) sums and one bilinear (Type II) sum. -/
theorem solution (U V : ℝ) (F : ℕ → ℂ) (N : ℕ)
    (hFN : ∀ n, N ≤ n → F n = 0)
    (hFV : ∀ n : ℕ, (n : ℝ) ≤ V → F n = 0) :
    ∑ n ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * F n
      = (∑ d ∈ Finset.range N, ∑ m ∈ Finset.range N,
            ((truncLe U moebiusR d : ℝ) : ℂ) *
              ((ArithmeticFunction.log m : ℝ) : ℂ) * F (d * m))
        - (∑ d ∈ Finset.range N, ∑ m ∈ Finset.range N,
            (((truncLe U moebiusR * truncLe V ArithmeticFunction.vonMangoldt) d : ℝ) : ℂ) *
              ((zetaR m : ℝ) : ℂ) * F (d * m))
        + (∑ d ∈ Finset.range N, ∑ w ∈ Finset.range N,
            ((truncGt U moebiusR d : ℝ) : ℂ) *
              (((truncGt V ArithmeticFunction.vonMangoldt * zetaR) w : ℝ) : ℂ) * F (d * w)) := by
  set A := truncLe U moebiusR with hA
  set B := truncGt U moebiusR with hB
  set C := truncLe V ArithmeticFunction.vonMangoldt with hC
  set D := truncGt V ArithmeticFunction.vonMangoldt with hD
  -- the identity, with the third term reassociated into Type II shape
  have hid : A * ArithmeticFunction.log - A * C * zetaR + B * (D * zetaR) + C
      = ArithmeticFunction.vonMangoldt := by
    rw [← mul_assoc]; exact TaoFivePrimes.vaughan_identity U V
  -- pointwise
  have hpt : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)
      = (A * ArithmeticFunction.log) n - (A * C * zetaR) n + (B * (D * zetaR)) n + C n := by
    intro n
    conv_lhs => rw [← hid]
    rfl
  -- split the sum
  have hsplit : ∑ n ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * F n
      = ∑ n ∈ Finset.range N,
          ((((A * ArithmeticFunction.log) n : ℝ) : ℂ) * F n
            - (((A * C * zetaR) n : ℝ) : ℂ) * F n
            + (((B * (D * zetaR)) n : ℝ) : ℂ) * F n
            + ((C n : ℝ) : ℂ) * F n) :=
    Finset.sum_congr rfl (fun n _ => by rw [hpt n]; push_cast; ring)
  -- the last term vanishes: `C` lives below `V`, where `F` is zero
  have hzero : ∑ n ∈ Finset.range N, ((C n : ℝ) : ℂ) * F n = 0 := by
    refine Finset.sum_eq_zero (fun n _ => ?_)
    by_cases h : (n : ℝ) ≤ V
    · rw [hFV n h, mul_zero]
    · have : C n = 0 := by rw [hC, truncLe_apply, if_neg h]
      rw [this]; simp
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hzero, add_zero,
    TaoFivePrimes.sum_dirichlet_pairing A ArithmeticFunction.log F N hFN,
    TaoFivePrimes.sum_dirichlet_pairing (A * C) zetaR F N hFN,
    TaoFivePrimes.sum_dirichlet_pairing B (D * zetaR) F N hFN]
