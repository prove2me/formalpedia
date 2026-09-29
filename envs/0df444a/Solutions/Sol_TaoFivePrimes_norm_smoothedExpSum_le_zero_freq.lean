-- Prove2me | solution 1 for TaoFivePrimes.norm_smoothedExpSum_le_zero_freq
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:41:10.878993+00:00
-- url     : https://prove2.me/submissions/38a4ed75-be21-4348-ae89-5adaa531d3cd

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open Finset
open scoped ArithmeticFunction.vonMangoldt
open TaoFivePrimes

namespace TaoSym

theorem norm_expCircle (θ : ℝ) : ‖expCircle θ‖ = 1 := by
  unfold expCircle; rw [Complex.norm_exp]; norm_num

theorem conj_expCircle (θ : ℝ) : (starRingEnd ℂ) (expCircle θ) = expCircle (-θ) := by
  unfold expCircle
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

/-- **Tao, equation (4.2) (the trivial bound).**  For a non-negative cutoff,
`|S_{η,q₀}(x,α)| ≤ S_{η,q₀}(x,0)`. -/
theorem smoothedExpSum_le_zero_freq (eta : ℝ → ℝ) (q₀ : ℕ) (x alpha : ℝ)
    (hx : 1 ≤ x) (heta : ∀ t : ℝ, 0 ≤ eta t) (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ‖smoothedExpSum eta q₀ x alpha‖ ≤ ‖smoothedExpSum eta q₀ x 0‖ := by
  classical
  have hx0 : (0:ℝ) < x := by linarith
  set N : ℕ := ⌊x⌋₊ with hN
  have hvanish : ∀ n : ℕ, n ∉ Finset.range (N+1) → eta ((n : ℝ) / x) = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    refine hsupp _ ?_
    rw [lt_div_iff₀ hx0, one_mul]
    have h1 : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 := Nat.lt_floor_add_one x
    rw [← hN] at h2
    linarith
  have hsum : ∀ β : ℝ, smoothedExpSum eta q₀ x β
      = ∑ n ∈ Finset.range (N+1),
          (if Nat.Coprime n q₀ then
            (Λ n : ℂ) * expCircle (β * n) * (eta ((n : ℝ) / x) : ℂ) else 0) := by
    intro β
    refine tsum_eq_sum ?_
    intro n hn
    by_cases h : Nat.Coprime n q₀
    · rw [if_pos h]; simp [hvanish n hn]
    · rw [if_neg h]
  have hzero : smoothedExpSum eta q₀ x 0
      = ((∑ n ∈ Finset.range (N+1),
          (if Nat.Coprime n q₀ then (Λ n : ℝ) * eta ((n : ℝ) / x) else 0) : ℝ) : ℂ) := by
    rw [hsum 0]
    push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : Nat.Coprime n q₀
    · rw [if_pos h, if_pos h]
      unfold expCircle
      norm_num
    · rw [if_neg h, if_neg h, Complex.ofReal_zero]
  have hnn : (0:ℝ) ≤ ∑ n ∈ Finset.range (N+1),
      (if Nat.Coprime n q₀ then (Λ n : ℝ) * eta ((n : ℝ) / x) else 0) := by
    refine Finset.sum_nonneg (fun n _ => ?_)
    split
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (heta _)
    · exact le_rfl
  rw [hzero, Complex.norm_real, Real.norm_of_nonneg hnn, hsum alpha]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases h : Nat.Coprime n q₀
  · rw [if_pos h, if_pos h]
    simp only [norm_mul, norm_expCircle, mul_one]
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_real, Real.norm_of_nonneg (heta _)]
  · rw [if_neg h, if_neg h, norm_zero]


end TaoSym

theorem solution (eta : ℝ → ℝ) (q₀ : ℕ) (x alpha : ℝ)
    (hx : 1 ≤ x) (heta : ∀ t : ℝ, 0 ≤ eta t) (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ‖TaoFivePrimes.smoothedExpSum eta q₀ x alpha‖
      ≤ ‖TaoFivePrimes.smoothedExpSum eta q₀ x 0‖ :=
  TaoSym.smoothedExpSum_le_zero_freq eta q₀ x alpha hx heta hsupp
