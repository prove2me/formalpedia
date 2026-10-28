-- Prove2me | solution 1 for TaoFivePrimes.high_zero_reciprocal_cube_weight_65000
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:51:05.924813+00:00
-- url     : https://prove2.me/submissions/d6e11295-8d68-4eab-bb40-dca03478c4b5

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ShiftedLogarithmicTail
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_NumericalZeroTail

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

private lemma high_reciprocal_num :
    (2 * Real.log (H/(2*Real.pi)) + 1)/(8*Real.pi*H^2) +
      (18*Real.log H + 179)/H^3 ≤ (186/10^12:ℝ) := by
  have hl := ExplicitPNT.DusartTable1.Modules.NumericalZeroTail.1 H 12
    (by norm_num [H]) (by norm_num [H])
  norm_num at hl
  have hratio := log_ratio_le
  have hp : (628/25:ℝ) ≤ 8*Real.pi := by nlinarith [Real.pi_gt_d2]
  have h1 : (2*Real.log (H/(2*Real.pi))+1)/(8*Real.pi*H^2) ≤ (777/1000:ℝ)/H^2 := by
    apply (div_le_iff₀ (by dsimp [H]; positivity : 0 < 8*Real.pi*H^2)).2
    dsimp [H] at *
    norm_num at *
    nlinarith only [hratio,hp]
  have h2 : (18*Real.log H+179)/H^3 ≤ (395:ℝ)/H^3 := by
    apply div_le_div_of_nonneg_right (by linarith) (by dsimp [H]; positivity)
  dsimp [H] at h1 h2 ⊢
  norm_num at h1 h2 ⊢
  linarith only [h1,h2]

theorem solution (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, 65000 < |ρ.im|) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤ (372/10^12:ℝ) := by
  classical
  let W : ℝ → ℝ := fun t => if H < t then 1/t^3 else 0
  have hpos (S : Finset ℂ) (hS : ∀ ρ ∈ S, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ (186/10^12:ℝ) := by
    let F := S.filter (fun ρ => H < ρ.im)
    have hF : ∀ ρ ∈ F, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
      intro ρ hρ
      exact hS ρ (Finset.mem_filter.mp hρ).1
    have hh := ExplicitPNT.DusartTable1.Modules.ShiftedLogarithmicTail.2 F hF H
      (by norm_num [H]) (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    have hb := hh.trans high_reciprocal_num
    simpa only [F, W, Finset.sum_filter, mul_ite, mul_zero] using hb
  have hh := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 W
    (186/10^12:ℝ) hpos Z hZ
  have he : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * W |ρ.im|) =
      ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [W, if_pos (show H < |ρ.im| by simpa [H] using hγ ρ hρ)]
  rw [he] at hh
  nlinarith only [hh]
