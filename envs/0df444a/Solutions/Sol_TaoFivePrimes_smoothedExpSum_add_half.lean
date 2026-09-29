-- Prove2me | solution 1 for TaoFivePrimes.smoothedExpSum_add_half
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:41:10.312272+00:00
-- url     : https://prove2.me/submissions/02bb2f1d-6955-4bdb-a40c-a3d5ce6adc59

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

/-- **Tao, equation (4.5) (self-adjointness).**  `S_{η,q}(x,-α) = conj S_{η,q}(x,α)`. -/
theorem smoothedExpSum_conj (eta : ℝ → ℝ) (q₀ : ℕ) (x alpha : ℝ) :
    smoothedExpSum eta q₀ x (-alpha) = (starRingEnd ℂ) (smoothedExpSum eta q₀ x alpha) := by
  unfold smoothedExpSum
  rw [starRingEnd_apply, tsum_star]
  refine tsum_congr (fun n => ?_)
  by_cases h : Nat.Coprime n q₀
  · rw [if_pos h, if_pos h]
    rw [RCLike.star_def, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      conj_expCircle]
    congr 2
    ring_nf
  · rw [if_neg h, if_neg h, star_zero]

/-- **Tao, equation (4.6) (anti-symmetry).**  If `q₀` is even then
`S_{η,q₀}(x, α + 1/2) = - S_{η,q₀}(x, α)`. -/
theorem smoothedExpSum_half (eta : ℝ → ℝ) (q₀ : ℕ) (hq : 2 ∣ q₀) (x alpha : ℝ) :
    smoothedExpSum eta q₀ x (alpha + 1/2) = - smoothedExpSum eta q₀ x alpha := by
  unfold smoothedExpSum
  rw [← tsum_neg]
  refine tsum_congr (fun n => ?_)
  by_cases h : Nat.Coprime n q₀
  · rw [if_pos h, if_pos h]
    have hodd : ¬ (2 ∣ n) := by
      intro h2
      have : (2:ℕ) ∣ Nat.gcd n q₀ := Nat.dvd_gcd h2 hq
      rw [Nat.Coprime] at h
      omega
    have hphase : expCircle ((alpha + 1/2) * n) = - expCircle (alpha * n) := by
      unfold expCircle
      obtain ⟨k, hkeq⟩ : ∃ k : ℕ, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      subst hkeq
      push_cast
      rw [show (2 * (Real.pi:ℂ) * Complex.I * (((alpha:ℂ) + 1/2) * (2 * (k:ℂ) + 1)))
          = 2 * (Real.pi:ℂ) * Complex.I * ((alpha:ℂ) * (2 * (k:ℂ) + 1))
            + ((k : ℤ) : ℂ) * (2 * (Real.pi:ℂ) * Complex.I) + (Real.pi:ℂ) * Complex.I by
        push_cast; ring]
      rw [Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
        Complex.exp_pi_mul_I]
      ring
    rw [hphase]
    ring
  · rw [if_neg h, if_neg h, neg_zero]


end TaoSym

theorem solution (eta : ℝ → ℝ) (q₀ : ℕ) (hq : 2 ∣ q₀) (x alpha : ℝ) :
    TaoFivePrimes.smoothedExpSum eta q₀ x (alpha + 1/2)
      = - TaoFivePrimes.smoothedExpSum eta q₀ x alpha :=
  TaoSym.smoothedExpSum_half eta q₀ hq x alpha
