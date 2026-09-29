-- Prove2me | solution 1 for TaoFivePrimes.smoothedExpSum_conj
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:41:09.47587+00:00
-- url     : https://prove2.me/submissions/994f99b9-9817-40d0-a2e6-ecf0c321cd48

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


end TaoSym

theorem solution (eta : ℝ → ℝ) (q₀ : ℕ) (x alpha : ℝ) :
    TaoFivePrimes.smoothedExpSum eta q₀ x (-alpha)
      = (starRingEnd ℂ) (TaoFivePrimes.smoothedExpSum eta q₀ x alpha) :=
  TaoSym.smoothedExpSum_conj eta q₀ x alpha
