-- Prove2me | solution 1 for TaoFivePrimes.rh100to1000_exp_centers
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T06:10:25.206755+00:00
-- url     : https://prove2.me/submissions/b84d8439-14e6-4d22-b96f-8132cf8a41b8

import Mathlib
import Definitions.Def_TaoFivePrimes_RH100To1000ExpCenters
import Definitions.Def_TaoFivePrimes_RH100To1000MellinModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RHExpCentersProof
open Finset
noncomputable def qsum : ℚ := ∑ n ∈ range 400, (3/16:ℚ)^n/(n.factorial:ℚ)
lemma qsum_cast : (qsum:ℝ)=∑ n ∈ range 400, (3/16:ℝ)^n/(n.factorial:ℝ) := by
  simp [qsum]
lemma sum_bounds : (TaoFivePrimes_RH100To1000ExpBaseNumerator:ℚ)/10^800+1/10^1000 < qsum ∧
    qsum+1/10^1000 < (TaoFivePrimes_RH100To1000ExpBaseNumerator+1:ℚ)/10^800 := by
  unfold TaoFivePrimes_RH100To1000ExpBaseNumerator qsum
  norm_num only [Nat.cast_ofNat]
  decide
lemma root_bounds : (TaoFivePrimes_RH100To1000ExpBaseNumerator:ℝ)/10^800 ≤ Real.exp (3/16) ∧
    Real.exp (3/16) ≤ (TaoFivePrimes_RH100To1000ExpBaseNumerator+1:ℝ)/10^800 := by
  have hb := Real.exp_bound (x:=(3/16:ℝ)) (by norm_num) (n:=400) (by norm_num)
  have he : |(3/16:ℝ)|^400*(401/((400).factorial*400)) ≤ 1/10^1000 := by norm_num [Nat.factorial]
  have hs := sum_bounds
  have hlo : (TaoFivePrimes_RH100To1000ExpBaseNumerator:ℝ)/10^800+1/10^1000 < (qsum:ℝ) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr hs.1
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] using h
  have hhi : (qsum:ℝ)+1/10^1000 < (TaoFivePrimes_RH100To1000ExpBaseNumerator+1:ℝ)/10^800 := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr hs.2
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] using h
  rw [←qsum_cast] at hb
  have hh := abs_sub_le_iff.mp (hb.trans he)
  constructor <;> linarith
lemma root_error : |Real.exp (3/16)-(TaoFivePrimes_RH100To1000ExpBaseNumerator:ℝ)/10^800| ≤ 1/10^800 := by
  have h := root_bounds
  rw [abs_sub_le_iff]
  push_cast at h
  constructor <;> linarith
lemma root_small : Real.exp (3/16) ≤ 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x:=(3/16:ℝ)) (by norm_num) (by norm_num)
  norm_num at h
  linarith
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
lemma center_error (i : ℕ) (hi : i < 16) :
    |Real.exp (RH1000Mellin.center i)-TaoFivePrimes_RH100To1000ExpCenter i| ≤ 1/10^780 := by
  let q : ℝ := (TaoFivePrimes_RH100To1000ExpBaseNumerator:ℝ)/10^800
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq2 : |q| ≤ 2 := by
    rw [abs_of_nonneg hq0]
    exact root_bounds.1.trans root_small
  have hx2 : |Real.exp (3/16)| ≤ 2 := by rw [abs_of_pos (Real.exp_pos _)]; exact root_small
  have hp := power_error (Real.exp (3/16)) q hx2 hq2 (1/10^800) (by positivity) root_error (2*i+1)
  have hc : RH1000Mellin.center i=(2*i+1:ℕ)*(3/16:ℝ) := by unfold RH1000Mellin.center; push_cast; ring
  rw [hc,Real.exp_nat_mul]
  change |Real.exp (3/16)^(2*i+1)-q^(2*i+1)| ≤ _
  apply hp.trans
  have hn : 2*i+1 ≤ 31 := by omega
  have hnR : (2*i+1:ℕ) ≤ (31:ℝ) := by exact_mod_cast hn
  have hpow : (2:ℝ)^(2*i+1) ≤ 2^31 := pow_le_pow_right₀ (by norm_num) hn
  calc
    _ ≤ (31:ℝ)*2^31*(1/10^800) := by gcongr
    _ ≤ _ := by norm_num
end RHExpCentersProof

theorem solution (i : ℕ) (hi : i < 16) :
    |Real.exp (RH1000Mellin.center i)-TaoFivePrimes_RH100To1000ExpCenter i| ≤ 1/10^780 := RHExpCentersProof.center_error i hi
