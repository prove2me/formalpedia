-- Prove2me | solution 1 for TaoFivePrimes.rh100to1000_negative_exp_approximation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T06:15:05.754969+00:00
-- url     : https://prove2.me/submissions/8efb47b9-63a1-48b8-bcf7-14d649ab0c78

import Mathlib
import Definitions.Def_TaoFivePrimes_RH100To1000NegativeExpApproximation
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RHNegativeExpProof
open Finset
lemma power_error (x y : ℝ) (hx : |x| ≤ 2) (hy : |y| ≤ 2) (ε : ℝ) (hε : 0 ≤ ε)
    (he : |x-y| ≤ ε) (n : ℕ) : |x^n-y^n| ≤ n*2^n*ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,pow_succ]
    have eq : x^n*x-y^n*y=x*(x^n-y^n)+(x-y)*y^n := by ring
    rw [eq]
    calc
      _ ≤ |x*(x^n-y^n)|+|(x-y)*y^n| := abs_add_le _ _
      _ = |x| *|x^n-y^n|+|x-y| *|y|^n := by rw [abs_mul,abs_mul,abs_pow]
      _ ≤ 2*(n*2^n*ε)+ε*2^n := by gcongr
      _ ≤ (n+1)*2^(n+1)*ε := by
        rw [pow_succ]
        have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
        push_cast
        nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) n]
    all_goals simp only [Nat.cast_add,Nat.cast_one,le_refl]
lemma large_tail (x : ℝ) (hx : 4096 ≤ x) : Real.exp (-x) ≤ 1/10^1200 := by
  have hbase : (2:ℝ) ≤ Real.exp 1 := by have h := Real.add_one_le_exp (1:ℝ); norm_num at h; exact h
  have hp : (2:ℝ)^4096 ≤ Real.exp 4096 := by
    calc
      _ ≤ (Real.exp 1)^4096 := pow_le_pow_left₀ (by positivity) hbase 4096
      _ = _ := by rw [←Real.exp_nat_mul]; norm_num
  calc
    Real.exp (-x) ≤ Real.exp (-4096) := Real.exp_le_exp.mpr (by linarith)
    _ = 1/Real.exp 4096 := by rw [Real.exp_neg,one_div]
    _ ≤ 1/(2:ℝ)^4096 := one_div_le_one_div_of_le (by positivity) hp
    _ ≤ _ := by norm_num
lemma bounded_error (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 4096) :
    |Real.exp (-x)-(∑ n ∈ range 1024, (-x/4096)^n/(n.factorial:ℝ))^4096| ≤ 1/10^1200 := by
  let y : ℝ := -x/4096
  let q : ℝ := ∑ n ∈ range 1024, y^n/(n.factorial:ℝ)
  have hy : |y| ≤ 1 := by dsimp [y]; rw [abs_div,abs_neg,abs_of_nonneg hx0]; norm_num; linarith
  have hb := Real.exp_bound hy (n:=1024) (by norm_num)
  have hrem : |Real.exp y-q| ≤ 1/10^2500 := by
    apply hb.trans
    calc
      _ ≤ 1*((1025:ℝ)/(((1024).factorial:ℝ)*1024)) := by
        apply mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hy)
        positivity
      _ ≤ _ := by norm_num [Nat.factorial]
  have hyn : |Real.exp y| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    have h : y ≤ 0 := by dsimp [y]; linarith
    exact (Real.exp_le_exp.mpr h).trans_eq Real.exp_zero
  have hq : |q| ≤ 2 := by
    have h := abs_sub (Real.exp y) (Real.exp y-q)
    have hε : (1/10^2500:ℝ) ≤ 1 := by norm_num
    have eq : Real.exp y-(Real.exp y-q)=q := by ring
    rw [eq] at h
    linarith
  have hp := power_error (Real.exp y) q (hyn.trans (by norm_num)) hq
    (1/10^2500) (by positivity) hrem 4096
  have he : -x=(4096:ℕ)*y := by dsimp [y]; norm_num; ring
  have ee : Real.exp (-x)=Real.exp y^4096 := by rw [he,Real.exp_nat_mul]
  rw [ee]
  change |Real.exp y^4096-q^4096| ≤ _
  apply hp.trans
  norm_num
lemma negative_exp_error (x : ℝ) (hx : 0 ≤ x) :
    |Real.exp (-x)-TaoFivePrimes_RH100To1000NegativeExpApproximation x| ≤ 1/10^1200 := by
  unfold TaoFivePrimes_RH100To1000NegativeExpApproximation
  split_ifs with h
  · exact bounded_error x hx h
  · rw [sub_zero,abs_of_pos (Real.exp_pos _)]
    exact large_tail x (le_of_not_ge h)
end RHNegativeExpProof

theorem solution (x : ℝ) (hx : 0 ≤ x) :
    |Real.exp (-x)-TaoFivePrimes_RH100To1000NegativeExpApproximation x| ≤ 1/10^1200 := RHNegativeExpProof.negative_exp_error x hx
