-- Prove2me | solution 1 for TaoFivePrimes.smoothedExpSum_zero_le_sup_mul_psi
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:14:32.426385+00:00
-- url     : https://prove2.me/submissions/d68f1b0f-b055-4061-b0da-9d8eada1a8c4

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open TaoFivePrimes

namespace TaoL43

theorem norm_expCircle (θ : ℝ) : ‖expCircle θ‖ = 1 := by
  unfold expCircle
  rw [Complex.norm_exp]
  norm_num

/-- **Tao, Lemma 4.3 (first inequality of (4.4)).**
`S_{η,q₀}(x,0) ≤ ‖η‖_{L^∞} · S_{1_{[0,1]},1}(x,0) = ‖η‖_{L^∞} ψ(x)`. -/
theorem smoothedExpSum_zero_le (eta : ℝ → ℝ) (M : ℝ) (q₀ : ℕ) (x : ℝ)
    (hx : 1 ≤ x) (hM : ∀ t : ℝ, |eta t| ≤ M)
    (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ‖smoothedExpSum eta q₀ x 0‖ ≤ M * Chebyshev.psi x := by
  classical
  have hx0 : (0:ℝ) < x := by linarith
  set N : ℕ := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hvanish : ∀ n : ℕ, n ∉ Finset.range (N+1) → eta ((n : ℝ) / x) = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    refine hsupp _ ?_
    rw [lt_div_iff₀ hx0, one_mul]
    have h1 : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 := Nat.lt_floor_add_one x
    rw [← hN] at h2
    linarith
  have hsum : smoothedExpSum eta q₀ x 0
      = ∑ n ∈ Finset.range (N+1),
          (if Nat.Coprime n q₀ then
            (Λ n : ℂ) * expCircle (0 * n) * (eta ((n : ℝ) / x) : ℂ) else 0) := by
    refine tsum_eq_sum ?_
    intro n hn
    by_cases h : Nat.Coprime n q₀
    · rw [if_pos h]; simp [hvanish n hn]
    · rw [if_neg h]
  rw [hsum]
  refine le_trans (norm_sum_le _ _) ?_
  have hMnn : (0:ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hbd : ∀ n ∈ Finset.range (N+1),
      ‖(if Nat.Coprime n q₀ then
          (Λ n : ℂ) * expCircle (0 * n) * (eta ((n : ℝ) / x) : ℂ) else 0)‖
        ≤ M * (Λ n : ℝ) := by
    intro n _
    by_cases h : Nat.Coprime n q₀
    · rw [if_pos h]
      simp only [norm_mul, norm_expCircle, mul_one]
      have h1 : ‖((Λ n : ℝ) : ℂ)‖ = (Λ n : ℝ) := by
        rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have h2 : ‖((eta ((n:ℝ)/x) : ℝ) : ℂ)‖ ≤ M := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hM _
      rw [h1, mul_comm]
      exact mul_le_mul_of_nonneg_right h2 ArithmeticFunction.vonMangoldt_nonneg
    · rw [if_neg h, norm_zero]
      exact mul_nonneg hMnn ArithmeticFunction.vonMangoldt_nonneg
  refine le_trans (Finset.sum_le_sum hbd) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hMnn
  -- `∑_{n ≤ ⌊x⌋} Λ(n) = ψ(x)`
  rw [Chebyshev.psi]
  refine le_of_eq ?_
  rw [← hN]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_range] at hn ⊢
    omega
  · intro n hn hn'
    simp only [Finset.mem_range, Finset.mem_Ioc, not_and_or, not_lt, not_le] at hn hn'
    have : n = 0 := by omega
    subst this
    simp

end TaoL43

theorem solution (eta : ℝ → ℝ) (M : ℝ) (q₀ : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hM : ∀ t : ℝ, |eta t| ≤ M)
    (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ‖TaoFivePrimes.smoothedExpSum eta q₀ x 0‖ ≤ M * Chebyshev.psi x :=
  TaoL43.smoothedExpSum_zero_le eta M q₀ x hx hM hsupp
