-- Prove2me | solution 1 for TaoFivePrimes.low_zero_reciprocal_weight_65000
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:48:16.27246+00:00
-- url     : https://prove2.me/submissions/7f656502-9bc0-42c6-8aaa-1fab59d5c998

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_LowZeroReciprocal

set_option autoImplicit false
set_option maxHeartbeats 2000000
open DusartSmoothing Complex Set

private def H : ℝ := 65000

private lemma log_ratio_le : Real.log (H / (2*Real.pi)) ≤ 37/4 := by
  have he9 : (8100:ℝ) ≤ Real.exp 9 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 9
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    linarith
  have hequarter : (493/384:ℝ) ≤ Real.exp (1/4) := by
    have hp := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1/4 by norm_num) 4
    norm_num [Finset.sum_range_succ] at hp
    exact hp
  have hp := mul_le_mul he9 hequarter (by norm_num) (Real.exp_nonneg 9)
  have he : Real.exp 9 * Real.exp (1/4) = Real.exp (37/4) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he] at hp
  have hratio : H/(2*Real.pi) ≤ (10351:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).2
    dsimp [H]
    nlinarith [Real.pi_gt_d2]
  have harg : 0 < H/(2*Real.pi) := by dsimp [H]; positivity
  apply (Real.log_le_iff_le_exp harg).2
  linarith

private lemma log14_le_eight_thirds : Real.log 14 ≤ 8/3 := by
  have he : (14:ℝ) ≤ Real.exp (8/3) := by
    have hp := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 8/3 by norm_num) 7
    norm_num [Finset.sum_range_succ] at hp
    linarith
  exact (Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 14)).2 he

private lemma low_reciprocal_num :
    (Real.log (H/(2*Real.pi)))^2/(4*Real.pi) - 1/(4*Real.pi) +
      (9*Real.log 14+91)/14 ≤ (301/20:ℝ) := by
  have harg : 1 ≤ H/(2*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).2
    dsimp [H]
    nlinarith [Real.pi_lt_four]
  have hlo : 0 ≤ Real.log (H/(2*Real.pi)) := Real.log_nonneg harg
  have hsq := pow_le_pow_left₀ hlo log_ratio_le 2
  have hratio : (Real.log (H/(2*Real.pi)))^2/(4*Real.pi) ≤ (341/50:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).2
    nlinarith only [hsq, Real.pi_gt_d2]
  have hrecip : (1/16:ℝ) ≤ 1/(4*Real.pi) := by
    apply one_div_le_one_div_of_le (by positivity : 0 < 4*Real.pi)
    linarith [Real.pi_lt_four]
  linarith [log14_le_eight_thirds]

theorem solution (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, |ρ.im| ≤ 65000) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|)) ≤ (301/10:ℝ) := by
  classical
  let W : ℝ → ℝ := fun t => if t ≤ H then 1/t else 0
  have hpos (S : Finset ℂ) (hS : ∀ ρ ∈ S, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ (301/20:ℝ) := by
    let F := S.filter (fun ρ => ρ.im ≤ H)
    have hF : ∀ ρ ∈ F, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
      intro ρ hρ
      exact hS ρ (Finset.mem_filter.mp hρ).1
    have hh := ExplicitPNT.DusartTable1.Modules.LowZeroReciprocal F hF H (by norm_num [H])
      (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    have hs : (∑ ρ ∈ F, (RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤ (301/20:ℝ) :=
      hh.trans low_reciprocal_num
    simpa only [F, W, Finset.sum_filter, mul_ite, mul_zero] using hs
  have hh := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 W (301/20:ℝ) hpos Z hZ
  have he : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * W |ρ.im|) =
      ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [W, if_pos (show |ρ.im| ≤ H by simpa [H] using hγ ρ hρ)]
  rw [he] at hh
  norm_num at hh ⊢
  exact hh
