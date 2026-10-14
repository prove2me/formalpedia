-- Prove2me | solution 1 for TaoFivePrimes.rh100to1000_theta_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T06:18:24.940966+00:00
-- url     : https://prove2.me/submissions/b4544f06-72e3-4411-b4c2-82e3a3cab634

import Mathlib
import Definitions.Def_TaoFivePrimes_RH100To1000ThetaAmplitude
import Theorems.Thm_TaoFivePrimes_rh_pi_enclosure_700
import Theorems.Thm_TaoFivePrimes_rh100to1000_exp_centers
import Theorems.Thm_TaoFivePrimes_rh100to1000_negative_exp_approximation
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RHThetaAmplitudeProof
open Finset
lemma negative_exp_transfer (a b : ℝ) (hb : 0 ≤ b) (h : |a-b| ≤ 1) :
    |Real.exp (-a)-Real.exp (-b)| ≤ 2*|a-b| := by
  have he : Real.exp (-a)-Real.exp (-b)=Real.exp (-b)*(Real.exp (b-a)-1) := by
    rw [show -a=-b+(b-a) by ring,Real.exp_add]
    ring
  have hδ : |b-a| ≤ 1 := by simpa only [abs_sub_comm] using h
  have ht := Real.abs_exp_sub_one_le hδ
  have hsmall : |Real.exp (-b)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_exp.mpr (by linarith)).trans_eq Real.exp_zero
  rw [he,abs_mul]
  calc
    _ ≤ 1*(2*|b-a|) := mul_le_mul hsmall ht (abs_nonneg _) (by norm_num)
    _ = _ := by rw [abs_sub_comm]; ring
lemma center_candidate_bound (i : ℕ) (hi : i < 16) :
    0 ≤ TaoFivePrimes_RH100To1000ExpCenter i ∧ TaoFivePrimes_RH100To1000ExpCenter i ≤ 2^31 := by
  unfold TaoFivePrimes_RH100To1000ExpCenter
  have hq0 : (0:ℝ) ≤ (TaoFivePrimes_RH100To1000ExpBaseNumerator:ℝ)/10^800 := by positivity
  have hq2 : (TaoFivePrimes_RH100To1000ExpBaseNumerator:ℝ)/10^800 ≤ 2 := by
    norm_num [TaoFivePrimes_RH100To1000ExpBaseNumerator]
  constructor
  · positivity
  · exact (pow_le_pow_left₀ hq0 hq2 (2*i+1)).trans (pow_le_pow_right₀ (by norm_num) (show 2*i+1 ≤ 31 by omega))
lemma amplitude_error (m : ℕ) (hm : m < 20) (i : ℕ) (hi : i < 16) :
    |Real.exp (-Real.pi*(m+1)^2*Real.exp (RH1000Mellin.center i))-
      TaoFivePrimes_RH100To1000ThetaAmplitude m i| ≤ 1/10^680 := by
  let p : ℝ := (TaoFivePrimes_RHPi700Numerator:ℝ)/10^700
  let q : ℝ := TaoFivePrimes_RH100To1000ExpCenter i
  let a : ℝ := Real.pi*(m+1)^2*Real.exp (RH1000Mellin.center i)
  let b : ℝ := p*(m+1)^2*q
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp := TaoFivePrimes.rh_pi_enclosure_700
  have hpe : |Real.pi-p| ≤ 1/10^700 := by
    rw [abs_sub_le_iff]
    dsimp [p]
    push_cast at hp
    constructor <;> linarith
  have hpi : |Real.pi| ≤ 4 := by rw [abs_of_pos Real.pi_pos]; exact Real.pi_lt_four.le
  have hq := center_candidate_bound i hi
  have he := TaoFivePrimes.rh100to1000_exp_centers i hi
  have hn0 : (0:ℝ) ≤ (m+1)^2 := sq_nonneg _
  have hn : (m+1:ℝ)^2 ≤ 400 := by
    have hmR : (m:ℝ) ≤ 19 := by exact_mod_cast (show m ≤ 19 by omega)
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have harg : |a-b| ≤ 1/10^686 := by
    have eq : a-b=(m+1)^2*(Real.pi*(Real.exp (RH1000Mellin.center i)-q)+(Real.pi-p)*q) := by dsimp [a,b]; ring
    rw [eq,abs_mul,abs_of_nonneg hn0]
    calc
      _ ≤ 400*(|Real.pi*(Real.exp (RH1000Mellin.center i)-q)|+|(Real.pi-p)*q|) :=
        mul_le_mul hn (abs_add_le _ _) (abs_nonneg _) (by norm_num)
      _ = 400*(|Real.pi| *|Real.exp (RH1000Mellin.center i)-q|+|Real.pi-p| *|q|) := by rw [abs_mul,abs_mul]
      _ ≤ 400*(4*(1/10^780)+(1/10^700)*2^31) := by
        dsimp [q] at *
        rw [abs_of_nonneg hq.1]
        gcongr
        all_goals first | exact hq.1 | exact hq.2
      _ ≤ _ := by norm_num
  have hb0 : 0 ≤ b := mul_nonneg (mul_nonneg hp0 hn0) hq.1
  have hδ := negative_exp_transfer a b hb0 (harg.trans (by norm_num))
  have hnum := TaoFivePrimes.rh100to1000_negative_exp_approximation b hb0
  have eq : -Real.pi*(m+1)^2*Real.exp (RH1000Mellin.center i)=-a := by dsimp [a]; ring
  rw [eq]
  change |Real.exp (-a)-TaoFivePrimes_RH100To1000NegativeExpApproximation b| ≤ _
  calc
    _ ≤ |Real.exp (-a)-Real.exp (-b)|+|Real.exp (-b)-TaoFivePrimes_RH100To1000NegativeExpApproximation b| := abs_sub_le _ _ _
    _ ≤ 2*(1/10^686)+1/10^1200 := add_le_add (hδ.trans (by gcongr)) hnum
    _ ≤ _ := by norm_num
end RHThetaAmplitudeProof

theorem solution (m : ℕ) (hm : m < 20) (i : ℕ) (hi : i < 16) :
    |Real.exp (-Real.pi*(m+1)^2*Real.exp (RH1000Mellin.center i))-
      TaoFivePrimes_RH100To1000ThetaAmplitude m i| ≤ 1/10^680 := RHThetaAmplitudeProof.amplitude_error m hm i hi
