-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_13
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:51:36.476487+00:00
-- url     : https://prove2.me/submissions/723f1f60-c4f9-45c7-a3d2-981353ac161a

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+156))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+156)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+156):ℝ)/10000 := by
  fin_cases i
  ·
    have hx : |x - (573803395/9244998:ℝ)| ≤ (44717019/250000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (573803395/9244998:ℝ) - (20:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (765490807/1000000000:ℝ) ≤ |(573803395/9244998:ℝ) - (20:ℝ)*Real.pi| ∧
        |(573803395/9244998:ℝ) - (20:ℝ)*Real.pi| ≤ (95686351/125000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (573803395/9244998:ℝ) (765490807/1000000000:ℝ) (95686351/125000000:ℝ) (44717019/250000000:ℝ)
      20 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((95686351/125000000:ℝ) - (765490807/1000000000:ℝ)^3/6 + (95686351/125000000:ℝ)^5/100)^2 + (44717019/250000000:ℝ) ≤ (6597/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (576576895/9244998:ℝ)| ≤ (179007611/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (576576895/9244998:ℝ) - (20:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (232745371/500000000:ℝ) ≤ |(576576895/9244998:ℝ) - (20:ℝ)*Real.pi| ∧
        |(576576895/9244998:ℝ) - (20:ℝ)*Real.pi| ≤ (465490743/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (576576895/9244998:ℝ) (232745371/500000000:ℝ) (465490743/1000000000:ℝ) (179007611/1000000000:ℝ)
      20 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((465490743/1000000000:ℝ) - (232745371/500000000:ℝ)^3/6 + (465490743/1000000000:ℝ)^5/100)^2 + (179007611/1000000000:ℝ) ≤ (3806/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (579350395/9244998:ℝ)| ≤ (89573573/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (579350395/9244998:ℝ) - (20:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (165490677/1000000000:ℝ) ≤ |(579350395/9244998:ℝ) - (20:ℝ)*Real.pi| ∧
        |(579350395/9244998:ℝ) - (20:ℝ)*Real.pi| ≤ (82745339/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (579350395/9244998:ℝ) (165490677/1000000000:ℝ) (82745339/500000000:ℝ) (89573573/500000000:ℝ)
      20 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((82745339/500000000:ℝ) - (165490677/1000000000:ℝ)^3/6 + (82745339/500000000:ℝ)^5/100)^2 + (89573573/500000000:ℝ) ≤ (2063/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (582123895/9244998:ℝ)| ≤ (179286681/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (582123895/9244998:ℝ) - (20:ℝ)*Real.pi := by linarith
    have hd : (134509387/1000000000:ℝ) ≤ |(582123895/9244998:ℝ) - (20:ℝ)*Real.pi| ∧
        |(582123895/9244998:ℝ) - (20:ℝ)*Real.pi| ≤ (33627347/250000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (582123895/9244998:ℝ) (134509387/1000000000:ℝ) (33627347/250000000:ℝ) (179286681/1000000000:ℝ)
      20 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((33627347/250000000:ℝ) - (134509387/1000000000:ℝ)^3/6 + (33627347/250000000:ℝ)^5/100)^2 + (179286681/1000000000:ℝ) ≤ (1973/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (584897395/9244998:ℝ)| ≤ (22428277/125000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (584897395/9244998:ℝ) - (20:ℝ)*Real.pi := by linarith
    have hd : (108627363/250000000:ℝ) ≤ |(584897395/9244998:ℝ) - (20:ℝ)*Real.pi| ∧
        |(584897395/9244998:ℝ) - (20:ℝ)*Real.pi| ≤ (434509453/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (584897395/9244998:ℝ) (108627363/250000000:ℝ) (434509453/1000000000:ℝ) (22428277/125000000:ℝ)
      20 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((434509453/1000000000:ℝ) - (108627363/250000000:ℝ)^3/6 + (434509453/1000000000:ℝ)^5/100)^2 + (22428277/125000000:ℝ) ≤ (3567/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (83952985/1320714:ℝ)| ≤ (179565751/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (83952985/1320714:ℝ) - (20:ℝ)*Real.pi := by linarith
    have hd : (183627379/250000000:ℝ) ≤ |(83952985/1320714:ℝ) - (20:ℝ)*Real.pi| ∧
        |(83952985/1320714:ℝ) - (20:ℝ)*Real.pi| ≤ (734509517/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (83952985/1320714:ℝ) (183627379/250000000:ℝ) (734509517/1000000000:ℝ) (179565751/1000000000:ℝ)
      20 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((734509517/1000000000:ℝ) - (183627379/250000000:ℝ)^3/6 + (734509517/1000000000:ℝ)^5/100)^2 + (179565751/1000000000:ℝ) ≤ (6293/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
  ·
    have hx : |x - (601538395/9244998:ℝ)| ≤ (7210537/40000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (601538395/9244998:ℝ) - (21:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (226770703/250000000:ℝ) ≤ |(601538395/9244998:ℝ) - (21:ℝ)*Real.pi| ∧
        |(601538395/9244998:ℝ) - (21:ℝ)*Real.pi| ≤ (907082813/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (601538395/9244998:ℝ) (226770703/250000000:ℝ) (907082813/1000000000:ℝ) (7210537/40000000:ℝ)
      21 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((907082813/1000000000:ℝ) - (226770703/250000000:ℝ)^3/6 + (907082813/1000000000:ℝ)^5/100)^2 + (7210537/40000000:ℝ) ≤ (8026/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (604311895/9244998:ℝ)| ≤ (2255037/12500000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (604311895/9244998:ℝ) - (21:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (607082747/1000000000:ℝ) ≤ |(604311895/9244998:ℝ) - (21:ℝ)*Real.pi| ∧
        |(604311895/9244998:ℝ) - (21:ℝ)*Real.pi| ≤ (151770687/250000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (604311895/9244998:ℝ) (607082747/1000000000:ℝ) (151770687/250000000:ℝ) (2255037/12500000:ℝ)
      21 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((151770687/250000000:ℝ) - (607082747/1000000000:ℝ)^3/6 + (151770687/250000000:ℝ)^5/100)^2 + (2255037/12500000:ℝ) ≤ (5061/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
