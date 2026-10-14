-- Prove2me | solution 1 for TaoFivePrimes.rh100to1000_phase_approximation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T06:12:59.798446+00:00
-- url     : https://prove2.me/submissions/bbc3e6db-6a0d-4eb2-ba5b-d0bc6d693ccb

import Mathlib
import Definitions.Def_TaoFivePrimes_RH100To1000PhaseApproximation
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RHPhaseApproximationProof
open Complex Finset
lemma power_error (x y : ℂ) (hx : ‖x‖ ≤ 2) (hy : ‖y‖ ≤ 2) (ε : ℝ) (hε : 0 ≤ ε)
    (he : ‖x-y‖ ≤ ε) (n : ℕ) : ‖x^n-y^n‖ ≤ n*2^n*ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,pow_succ]
    have eq : x^n*x-y^n*y=x*(x^n-y^n)+(x-y)*y^n := by ring
    rw [eq]
    calc
      _ ≤ ‖x*(x^n-y^n)‖+‖(x-y)*y^n‖ := norm_add_le _ _
      _ = ‖x‖*‖x^n-y^n‖+‖x-y‖*‖y‖^n := by rw [norm_mul,norm_mul,norm_pow]
      _ ≤ 2*(n*2^n*ε)+ε*2^n := by gcongr
      _ ≤ (n+1)*2^(n+1)*ε := by
        rw [pow_succ]
        have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
        push_cast
        nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) n]
    all_goals simp only [Nat.cast_add,Nat.cast_one,le_refl]
lemma phase_error (τ : ℝ) (hτ : |τ| ≤ 500) (i : ℕ) (hi : i < 16) :
    ‖Complex.exp (Complex.I*(τ:ℂ)*(RH1000Mellin.center i:ℂ))-
      TaoFivePrimes_RH100To1000PhaseApproximation τ i‖ ≤ 1/10^1200 := by
  let x : ℂ := Complex.I*(τ:ℂ)*(RH1000Mellin.center i:ℂ)/4096
  let q : ℂ := ∑ n ∈ range 1024, x^n/(n.factorial:ℂ)
  have hc0 : 0 ≤ RH1000Mellin.center i := by unfold RH1000Mellin.center; positivity
  have hc6 : RH1000Mellin.center i ≤ 6 := by
    unfold RH1000Mellin.center
    have hn : (i:ℝ) ≤ 15 := by exact_mod_cast (show i ≤ 15 by omega)
    linarith
  have hx : ‖x‖ ≤ 1 := by
    dsimp [x]
    rw [norm_div,norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Complex.norm_real]
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hc0]
    norm_num
    nlinarith
  have hb := Complex.exp_bound hx (n:=1024) (by norm_num)
  have hrem : ‖Complex.exp x-q‖ ≤ 1/10^2500 := by
    apply hb.trans
    calc
      _ ≤ 1*((1025:ℝ)*(((1024).factorial:ℝ)*1024)⁻¹) := by
        apply mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hx)
        positivity
      _ ≤ _ := by norm_num [Nat.factorial]
  have hxn : ‖Complex.exp x‖=1 := by
    rw [Complex.norm_exp]
    have hre : x.re=0 := by dsimp [x]; simp
    rw [hre,Real.exp_zero]
  have hq : ‖q‖ ≤ 2 := by
    have h := norm_sub_le (Complex.exp x) (Complex.exp x-q)
    have hε : (1/10^2500:ℝ) ≤ 1 := by norm_num
    have eq : Complex.exp x-(Complex.exp x-q)=q := by ring
    rw [eq,hxn] at h
    linarith
  have hp := power_error (Complex.exp x) q (by rw [hxn]; norm_num) hq
    (1/10^2500) (by positivity) hrem 4096
  have he : Complex.I*(τ:ℂ)*(RH1000Mellin.center i:ℂ)=(4096:ℕ)*x := by dsimp [x]; norm_num; ring
  rw [he,Complex.exp_nat_mul]
  change ‖Complex.exp x^4096-q^4096‖ ≤ _
  apply hp.trans
  norm_num
end RHPhaseApproximationProof

theorem solution (τ : ℝ) (hτ : |τ| ≤ 500) (i : ℕ) (hi : i < 16) :
    ‖Complex.exp (Complex.I*(τ:ℂ)*(RH1000Mellin.center i:ℂ))-
      TaoFivePrimes_RH100To1000PhaseApproximation τ i‖ ≤ 1/10^1200 := RHPhaseApproximationProof.phase_error τ hτ i hi
