-- Prove2me | solution 1 for TaoFivePrimes.sine_weight_tail_above_297200
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:01:27.275272+00:00
-- url     : https://prove2.me/submissions/20f28cc3-0de6-485b-9025-cc7643e5d20b

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ShiftedLogarithmicTail

set_option autoImplicit false
set_option maxHeartbeats 2000000
open DusartSmoothing Complex Set

private def H : ℝ := 297200

private lemma exp_ge_10 : (22026:ℝ) ≤ Real.exp 10 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 10
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_ge_12 : (162754:ℝ) ≤ Real.exp 12 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 12
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma log_ratio_le : Real.log (H/(2*Real.pi)) ≤ 54/5 := by
  have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 8/10 by norm_num) 4
  norm_num [Finset.sum_range_succ] at hf
  have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
  have hid : Real.exp 10 * Real.exp (8/10) = Real.exp (54/5) := by
    rw [←Real.exp_add]
    congr 1
    ring
  norm_num at hid
  rw [hid] at he
  have hratio : H/(2*Real.pi) ≤ (297200/(157/25):ℝ) := by
    dsimp [H]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith [Real.pi_gt_d2]
  apply (Real.log_le_iff_le_exp (by dsimp [H]; positivity : 0 < H/(2*Real.pi))).2
  norm_num at he hratio ⊢
  linarith

private lemma log_height_le : Real.log H ≤ 127/10 := by
  have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 7/10 by norm_num) 4
  norm_num [Finset.sum_range_succ] at hf
  have he := mul_le_mul exp_ge_12 hf (by norm_num) (Real.exp_nonneg 12)
  have hid : Real.exp 12 * Real.exp (7/10) = Real.exp (127/10) := by
    rw [←Real.exp_add]
    congr 1
    ring
  norm_num at hid
  rw [hid] at he
  apply (Real.log_le_iff_le_exp (by norm_num [H] : 0 < H)).2
  dsimp [H]
  norm_num at he ⊢
  linarith

private lemma tail_num :
    (2*Real.log (H/(2*Real.pi))+1)/(8*Real.pi*H^2) +
      (18*Real.log H+179)/H^3 ≤ (81609874820/(8*10^21):ℝ) := by
  have hnum : 2*Real.log (H/(2*Real.pi))+1 ≤ (2*(54/5)+1:ℝ) := by linarith [log_ratio_le]
  have hden : 8*(157/50:ℝ)*H^2 ≤ 8*Real.pi*H^2 := by
    have hp : (157/50:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
    nlinarith only [hp, sq_nonneg H]
  have h1 : (2*Real.log (H/(2*Real.pi))+1)/(8*Real.pi*H^2) ≤
      (2*(54/5)+1)/(8*(157/50:ℝ)*H^2) :=
    div_le_div₀ (by norm_num) hnum (by dsimp [H]; positivity) hden
  have h2 : (18*Real.log H+179)/H^3 ≤ (18*(127/10)+179:ℝ)/H^3 := by
    apply div_le_div_of_nonneg_right (by linarith [log_height_le]) (by dsimp [H]; positivity)
  dsimp [H] at h1 h2 ⊢
  norm_num at h1 h2 ⊢
  linarith only [h1,h2]

theorem solution (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, 297200 < |ρ.im|) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (4 / |ρ.im|^3)) ≤ (81609874820/10^21:ℝ) := by
  classical
  let W : ℝ → ℝ := fun t => if H < t then 1/t^3 else 0
  have hpos (S : Finset ℂ) (hS : ∀ ρ ∈ S, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ (81609874820/(8*10^21):ℝ) := by
    let F := S.filter (fun ρ => H < ρ.im)
    have hF : ∀ ρ ∈ F, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
      intro ρ hρ
      exact hS ρ (Finset.mem_filter.mp hρ).1
    have hh := ExplicitPNT.DusartTable1.Modules.ShiftedLogarithmicTail.2 F hF H
      (by norm_num [H]) (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    have hb := hh.trans tail_num
    simpa only [F, W, Finset.sum_filter, mul_ite, mul_zero] using hb
  have hh := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 W
    (81609874820/(8*10^21):ℝ) hpos Z hZ
  have he : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * W |ρ.im|) =
      ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [W, if_pos (show H < |ρ.im| by simpa [H] using hγ ρ hρ)]
  rw [he] at hh
  have hsum : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (4 / |ρ.im|^3)) =
      4*(∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    ring
  rw [hsum]
  nlinarith only [hh]
