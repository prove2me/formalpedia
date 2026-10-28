-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_completed_zeta_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:00:29.736984+00:00
-- url     : https://prove2.me/submissions/7a73a739-3dcd-42a5-b311-214f7476b0be

import Definitions.Def_TaoFivePrimes_RHDirect132XiCoefficients
import Theorems.Thm_TaoFivePrimes_rh_direct_folded_moment_derivative
import Theorems.Thm_TaoFivePrimes_rh_direct_132_rational_quadrature
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace DirectLambda132

lemma raw_conj (τ : ℝ) (n : ℕ) :
    RHDirectOscillatory.rawIntegral (-τ) n =
      star (RHDirectOscillatory.rawIntegral τ n) := by
  unfold RHDirectOscillatory.rawIntegral
  change _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [map_mul,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I,map_neg]
  congr 2
  push_cast
  ring

end DirectLambda132

theorem solution (n : ℕ) :
    ‖iteratedDeriv n completedRiemannZeta₀ ((1/2:ℂ)+132*Complex.I) /
        (n.factorial:ℂ) - RHDirect132XiCoefficients.lambda n‖ ≤
      (18/10^82)/(2:ℝ)^n := by
  have hf := TaoFivePrimes.rh_direct_folded_moment_derivative n 66
  norm_num only [Complex.ofReal_ofNat] at hf
  have hc : ((1/2:ℂ)+2*Complex.I*(66:ℂ))=((1/2:ℂ)+132*Complex.I) := by ring
  rw [hc,DirectLambda132.raw_conj] at hf
  rw [hf]
  unfold RHDirect132XiCoefficients.lambda
  have hid :
      (RHDirectOscillatory.rawIntegral 66 n+
        (-1:ℂ)^n*star (RHDirectOscillatory.rawIntegral 66 n))/(2:ℂ)^(n+1) -
      (RHDirect132Rule.rule n+(-1:ℂ)^n*star (RHDirect132Rule.rule n))/(2:ℂ)^(n+1) =
      ((RHDirectOscillatory.rawIntegral 66 n-RHDirect132Rule.rule n) +
        (-1:ℂ)^n*star (RHDirectOscillatory.rawIntegral 66 n-RHDirect132Rule.rule n)) /
        (2:ℂ)^(n+1) := by
    simp only [star_sub]
    ring
  rw [hid,norm_div,norm_pow]
  have hq := TaoFivePrimes.rh_direct_132_rational_quadrature n
  have hnum : ‖(RHDirectOscillatory.rawIntegral 66 n-RHDirect132Rule.rule n) +
        (-1:ℂ)^n*star (RHDirectOscillatory.rawIntegral 66 n-RHDirect132Rule.rule n)‖ ≤
      2*(18/10^82) := by
    have h := norm_add_le (RHDirectOscillatory.rawIntegral 66 n-RHDirect132Rule.rule n)
      ((-1:ℂ)^n*star (RHDirectOscillatory.rawIntegral 66 n-RHDirect132Rule.rule n))
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_star] at h
    linarith
  have hden : ‖(2:ℂ)‖^(n+1)=(2:ℝ)^(n+1) := by norm_num
  rw [hden]
  calc
    _ ≤ (2*(18/10^82))/(2:ℝ)^(n+1) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by rw [pow_succ]; ring
