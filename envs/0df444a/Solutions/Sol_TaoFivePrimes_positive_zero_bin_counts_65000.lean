-- Prove2me | solution 1 for TaoFivePrimes.positive_zero_bin_counts_65000
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:01:27.178527+00:00
-- url     : https://prove2.me/submissions/1d11d500-8df5-4bd6-abd2-1bc4cd790d42

import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Theorems.Thm_TaoFivePrimes_positive_zero_bin_count
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
open DusartSmoothing

private lemma count_from_exp (Z : Finset ℂ) (L U A qd qe C : ℝ)
    (hL : 65000 ≤ L) (hstep : U-L = 1290) (hU : U ≤ A)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ L < ρ.im ∧ ρ.im ≤ U)
    (heD : A/(157/25) ≤ Real.exp qd) (heE : A+5 ≤ Real.exp qe)
    (hqd : 0 ≤ qd) (hC : (1290/(157/25))*qd+18*qe+158 ≤ C) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤ C := by
  have hpi : (157/25:ℝ) ≤ 2*Real.pi := by nlinarith [Real.pi_gt_d2]
  have hUp : 0 < U := by linarith
  have hratio : U/(2*Real.pi) ≤ A/(157/25) := by
    calc
      _ ≤ U/(157/25) := div_le_div_of_nonneg_left hUp.le (by norm_num) hpi
      _ ≤ A/(157/25) := div_le_div_of_nonneg_right hU (by norm_num)
  have hdensity : Real.log (U/(2*Real.pi)) ≤ qd :=
    (Real.log_le_iff_le_exp (div_pos hUp (by positivity))).2 (hratio.trans heD)
  have herror : Real.log (U+5) ≤ qe :=
    (Real.log_le_iff_le_exp (by linarith : 0 < U+5)).2 (by linarith [heE])
  have hfactor0 : 0 ≤ (U-L)/(2*Real.pi) := by rw [hstep]; positivity
  have hfactor : (U-L)/(2*Real.pi) ≤ 1290/(157/25) := by
    rw [hstep]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi
  have h1 := mul_le_mul_of_nonneg_left hdensity hfactor0
  have h2 := mul_le_mul_of_nonneg_right hfactor hqd
  have hc := TaoFivePrimes.positive_zero_bin_count Z L U (by linarith) (by linarith) hZ
  linarith only [hc,h1,h2,herror,hC]

private lemma exp_ge_9 : (8103:ℝ) ≤ Real.exp 9 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 9
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_ge_10 : (22026:ℝ) ≤ Real.exp 10 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 10
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_ge_11 : (59874:ℝ) ≤ Real.exp 11 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 11
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_ge_12 : (162754:ℝ) ≤ Real.exp 12 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 12
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

theorem solution (i : Fin 15) (Z : Finset ℂ) (L U : ℝ)
    (hL : 65000 ≤ L) (hstep : U-L = 1290)
    (hU : U ≤ 80480+15480*(i.val:ℝ))
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ L < ρ.im ∧ ρ.im ≤ U) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤
      (TaoFivePrimes.sineBinCount65k (12*i.val):ℝ) := by
  fin_cases i
  ·
    have heD : (80480/(157/25):ℝ) ≤ Real.exp (95/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 5/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_9 hf (by norm_num) (Real.exp_nonneg 9)
      have hid : Real.exp 9 * Real.exp (5/10) = Real.exp (95/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (80480+5:ℝ) ≤ Real.exp (113/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 3/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_11 hf (by norm_num) (Real.exp_nonneg 11)
      have hid : Real.exp 11 * Real.exp (3/10) = Real.exp (113/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 80480 (95/10) (113/10) 2313 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (95960/(157/25):ℝ) ≤ Real.exp (97/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 7/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_9 hf (by norm_num) (Real.exp_nonneg 9)
      have hid : Real.exp 9 * Real.exp (7/10) = Real.exp (97/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (95960+5:ℝ) ≤ Real.exp (115/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 5/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_11 hf (by norm_num) (Real.exp_nonneg 11)
      have hid : Real.exp 11 * Real.exp (5/10) = Real.exp (115/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 95960 (97/10) (115/10) 2358 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (111440/(157/25):ℝ) ≤ Real.exp (98/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 8/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_9 hf (by norm_num) (Real.exp_nonneg 9)
      have hid : Real.exp 9 * Real.exp (8/10) = Real.exp (98/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (111440+5:ℝ) ≤ Real.exp (117/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 7/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_11 hf (by norm_num) (Real.exp_nonneg 11)
      have hid : Real.exp 11 * Real.exp (7/10) = Real.exp (117/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 111440 (98/10) (117/10) 2382 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (126920/(157/25):ℝ) ≤ Real.exp (100/10:ℝ) := by
      have he := exp_ge_10
      norm_num at he ⊢
      linarith
    have heE : (126920+5:ℝ) ≤ Real.exp (118/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 8/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_11 hf (by norm_num) (Real.exp_nonneg 11)
      have hid : Real.exp 11 * Real.exp (8/10) = Real.exp (118/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 126920 (100/10) (118/10) 2425 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (142400/(157/25):ℝ) ≤ Real.exp (101/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
      have hid : Real.exp 10 * Real.exp (1/10) = Real.exp (101/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (142400+5:ℝ) ≤ Real.exp (119/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 9/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_11 hf (by norm_num) (Real.exp_nonneg 11)
      have hid : Real.exp 11 * Real.exp (9/10) = Real.exp (119/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 142400 (101/10) (119/10) 2447 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (157880/(157/25):ℝ) ≤ Real.exp (102/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 2/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
      have hid : Real.exp 10 * Real.exp (2/10) = Real.exp (102/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (157880+5:ℝ) ≤ Real.exp (120/10:ℝ) := by
      have he := exp_ge_12
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 157880 (102/10) (120/10) 2470 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (173360/(157/25):ℝ) ≤ Real.exp (103/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 3/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
      have hid : Real.exp 10 * Real.exp (3/10) = Real.exp (103/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (173360+5:ℝ) ≤ Real.exp (121/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_12 hf (by norm_num) (Real.exp_nonneg 12)
      have hid : Real.exp 12 * Real.exp (1/10) = Real.exp (121/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 173360 (103/10) (121/10) 2492 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (188840/(157/25):ℝ) ≤ Real.exp (104/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 4/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
      have hid : Real.exp 10 * Real.exp (4/10) = Real.exp (104/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (188840+5:ℝ) ≤ Real.exp (122/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 2/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_12 hf (by norm_num) (Real.exp_nonneg 12)
      have hid : Real.exp 12 * Real.exp (2/10) = Real.exp (122/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 188840 (104/10) (122/10) 2514 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (204320/(157/25):ℝ) ≤ Real.exp (104/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 4/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
      have hid : Real.exp 10 * Real.exp (4/10) = Real.exp (104/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (204320+5:ℝ) ≤ Real.exp (123/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 3/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_12 hf (by norm_num) (Real.exp_nonneg 12)
      have hid : Real.exp 12 * Real.exp (3/10) = Real.exp (123/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 204320 (104/10) (123/10) 2516 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (219800/(157/25):ℝ) ≤ Real.exp (105/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 5/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
      have hid : Real.exp 10 * Real.exp (5/10) = Real.exp (105/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (219800+5:ℝ) ≤ Real.exp (124/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 4/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_12 hf (by norm_num) (Real.exp_nonneg 12)
      have hid : Real.exp 12 * Real.exp (4/10) = Real.exp (124/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 219800 (105/10) (124/10) 2539 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (235280/(157/25):ℝ) ≤ Real.exp (106/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 6/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
      have hid : Real.exp 10 * Real.exp (6/10) = Real.exp (106/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (235280+5:ℝ) ≤ Real.exp (124/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 4/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_12 hf (by norm_num) (Real.exp_nonneg 12)
      have hid : Real.exp 12 * Real.exp (4/10) = Real.exp (124/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 235280 (106/10) (124/10) 2559 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (250760/(157/25):ℝ) ≤ Real.exp (106/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 6/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
      have hid : Real.exp 10 * Real.exp (6/10) = Real.exp (106/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (250760+5:ℝ) ≤ Real.exp (125/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 5/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_12 hf (by norm_num) (Real.exp_nonneg 12)
      have hid : Real.exp 12 * Real.exp (5/10) = Real.exp (125/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 250760 (106/10) (125/10) 2561 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (266240/(157/25):ℝ) ≤ Real.exp (107/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 7/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
      have hid : Real.exp 10 * Real.exp (7/10) = Real.exp (107/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (266240+5:ℝ) ≤ Real.exp (125/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 5/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_12 hf (by norm_num) (Real.exp_nonneg 12)
      have hid : Real.exp 12 * Real.exp (5/10) = Real.exp (125/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 266240 (107/10) (125/10) 2581 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (281720/(157/25):ℝ) ≤ Real.exp (108/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 8/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
      have hid : Real.exp 10 * Real.exp (8/10) = Real.exp (108/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (281720+5:ℝ) ≤ Real.exp (126/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 6/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_12 hf (by norm_num) (Real.exp_nonneg 12)
      have hid : Real.exp 12 * Real.exp (6/10) = Real.exp (126/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 281720 (108/10) (126/10) 2604 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
  ·
    have heD : (297200/(157/25):ℝ) ≤ Real.exp (108/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 8/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_10 hf (by norm_num) (Real.exp_nonneg 10)
      have hid : Real.exp 10 * Real.exp (8/10) = Real.exp (108/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have heE : (297200+5:ℝ) ≤ Real.exp (127/10:ℝ) := by
      have hf := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 7/10 by norm_num) 4
      norm_num [Finset.sum_range_succ] at hf
      have he := mul_le_mul exp_ge_12 hf (by norm_num) (Real.exp_nonneg 12)
      have hid : Real.exp 12 * Real.exp (7/10) = Real.exp (127/10) := by
        rw [←Real.exp_add]
        congr 1
        ring
      norm_num at hid
      rw [hid] at he
      norm_num at he ⊢
      linarith
    have h := count_from_exp Z L U 297200 (108/10) (127/10) 2606 hL hstep
      (by norm_num at hU ⊢; exact hU) hZ heD heE (by norm_num) (by norm_num)
    simpa [TaoFivePrimes.sineBinCount65k] using h
