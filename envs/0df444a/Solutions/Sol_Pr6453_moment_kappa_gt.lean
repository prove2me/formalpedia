-- Prove2me | solution 1 for Pr6453.moment_kappa_gt
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T15:48:55.080012+00:00
-- url     : https://prove2.me/submissions/a8e7fcbb-d131-4c69-b2eb-c444e04bf1d2

/-
PR #6453, the moment inequality at the claimed saving.

`moment_kappa_gt` is proved from two ingredients:

* `log_r_bounds` — two-sided rational bounds on `Real.log r` for the 19 ranks of the
  two histograms.  Each is obtained from the Taylor series of `log (1 - x)` at
  `x = 1 - r/2^k` (`Real.abs_log_sub_add_sum_range_le`, %d terms) together with
  Mathlib's decimal bounds on `Real.log 2`.
* `pow_r_bounds` — two-sided rational bounds on `r^(1-κ)`, obtained from
  `r^(1-κ) = r * exp (-(κ log r))` (`Real.rpow_def_of_pos`, `Real.exp_add`,
  `Real.exp_log`) and `Real.exp_bound` at the two endpoints of the log interval,
  with six terms of the exponential series.

The final step is linear arithmetic over the rational constants: the certified
lower bound for `Σ (T_r - P_r) r^(1-κ)` is `0.0012745869`, against a true value
of `0.0012756146`.
-/
import Definitions.Def_Pr6453_RankMoments

namespace Pr6453

noncomputable section

open Finset

/-- `log 2 = 1 log 2`. -/
theorem log_2_bounds : (0.693147180300 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (0.693147180800 : ℝ) := by
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have e : Real.log (2:ℝ) = 1 * Real.log 2 := by
    rw [show (2:ℝ) = 2^1 by norm_num, Real.log_pow]; norm_num
  rw [e]
  constructor <;> linarith

/-- `log 3` to eleven decimal places. -/
theorem log_3_bounds : (1.098612288143 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (1.098612289154 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/4 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (3:ℝ) = Real.log (3/4) + 2 * Real.log 2 := by
    have h1 : Real.log ((3:ℝ)/4) = Real.log 3 - Real.log 4 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 4 = 2 log 2`. -/
theorem log_4_bounds : (1.386294360600 : ℝ) ≤ Real.log 4 ∧ Real.log 4 ≤ (1.386294361600 : ℝ) := by
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have e : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [e]
  constructor <;> linarith

/-- `log 5` to eleven decimal places. -/
theorem log_5_bounds : (1.609437911909 : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ (1.609437912919 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/4 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (5:ℝ) = Real.log (5/4) + 2 * Real.log 2 := by
    have h1 : Real.log ((5:ℝ)/4) = Real.log 5 - Real.log 4 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 6` to eleven decimal places. -/
theorem log_6_bounds : (1.791759468443 : ℝ) ≤ Real.log 6 ∧ Real.log 6 ≤ (1.791759469954 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/4 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (6:ℝ) = Real.log (6/8) + 3 * Real.log 2 := by
    have h1 : Real.log ((6:ℝ)/8) = Real.log 6 - Real.log 8 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 7` to eleven decimal places. -/
theorem log_7_bounds : (1.945910148275 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ (1.945910149776 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/8 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (7:ℝ) = Real.log (7/8) + 3 * Real.log 2 := by
    have h1 : Real.log ((7:ℝ)/8) = Real.log 7 - Real.log 8 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 8 = 3 log 2`. -/
theorem log_8_bounds : (2.079441540900 : ℝ) ≤ Real.log 8 ∧ Real.log 8 ≤ (2.079441542400 : ℝ) := by
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have e : Real.log (8:ℝ) = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
  rw [e]
  constructor <;> linarith

/-- `log 9` to eleven decimal places. -/
theorem log_9_bounds : (2.197224576556 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ (2.197224578057 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/8 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (9:ℝ) = Real.log (9/8) + 3 * Real.log 2 := by
    have h1 : Real.log ((9:ℝ)/8) = Real.log 9 - Real.log 8 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 16 = 4 log 2`. -/
theorem log_16_bounds : (2.772588721200 : ℝ) ≤ Real.log 16 ∧ Real.log 16 ≤ (2.772588723200 : ℝ) := by
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have e : Real.log (16:ℝ) = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
  rw [e]
  constructor <;> linarith

/-- `log 17` to eleven decimal places. -/
theorem log_17_bounds : (2.833213343016 : ℝ) ≤ Real.log 17 ∧ Real.log 17 ≤ (2.833213345017 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/16 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (17:ℝ) = Real.log (17/16) + 4 * Real.log 2 := by
    have h1 : Real.log ((17:ℝ)/16) = Real.log 17 - Real.log 16 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (16:ℝ) = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 24` to eleven decimal places. -/
theorem log_24_bounds : (3.178053829043 : ℝ) ≤ Real.log 24 ∧ Real.log 24 ≤ (3.178053831554 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/4 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (24:ℝ) = Real.log (24/32) + 5 * Real.log 2 := by
    have h1 : Real.log ((24:ℝ)/32) = Real.log 24 - Real.log 32 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (32:ℝ) = 5 * Real.log 2 := by
      rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 25` to eleven decimal places. -/
theorem log_25_bounds : (3.218875823568 : ℝ) ≤ Real.log 25 ∧ Real.log 25 ≤ (3.218875826069 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (7/32 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (25:ℝ) = Real.log (25/32) + 5 * Real.log 2 := by
    have h1 : Real.log ((25:ℝ)/32) = Real.log 25 - Real.log 32 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (32:ℝ) = 5 * Real.log 2 := by
      rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 32 = 5 log 2`. -/
theorem log_32_bounds : (3.465735901500 : ℝ) ≤ Real.log 32 ∧ Real.log 32 ≤ (3.465735904000 : ℝ) := by
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have e : Real.log (32:ℝ) = 5 * Real.log 2 := by
    rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]; norm_num
  rw [e]
  constructor <;> linarith

/-- `log 33` to eleven decimal places. -/
theorem log_33_bounds : (3.496507560166 : ℝ) ≤ Real.log 33 ∧ Real.log 33 ≤ (3.496507562667 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/32 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (33:ℝ) = Real.log (33/32) + 5 * Real.log 2 := by
    have h1 : Real.log ((33:ℝ)/32) = Real.log 33 - Real.log 32 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (32:ℝ) = 5 * Real.log 2 := by
      rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 56` to eleven decimal places. -/
theorem log_56_bounds : (4.025351689175 : ℝ) ≤ Real.log 56 ∧ Real.log 56 ≤ (4.025351692176 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/8 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (56:ℝ) = Real.log (56/64) + 6 * Real.log 2 := by
    have h1 : Real.log ((56:ℝ)/64) = Real.log 56 - Real.log 64 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (64:ℝ) = 6 * Real.log 2 := by
      rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 57` to eleven decimal places. -/
theorem log_57_bounds : (4.043051266274 : ℝ) ≤ Real.log 57 ∧ Real.log 57 ≤ (4.043051269275 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (7/64 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (57:ℝ) = Real.log (57/64) + 6 * Real.log 2 := by
    have h1 : Real.log ((57:ℝ)/64) = Real.log 57 - Real.log 64 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (64:ℝ) = 6 * Real.log 2 := by
      rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 73` to eleven decimal places. -/
theorem log_73_bounds : (4.290459439588 : ℝ) ≤ Real.log 73 ∧ Real.log 73 ≤ (4.290459442589 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-9/64 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (73:ℝ) = Real.log (73/64) + 6 * Real.log 2 := by
    have h1 : Real.log ((73:ℝ)/64) = Real.log 73 - Real.log 64 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (64:ℝ) = 6 * Real.log 2 := by
      rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `log 145` to eleven decimal places. -/
theorem log_145_bounds : (4.976733740600 : ℝ) ≤ Real.log 145 ∧ Real.log 145 ≤ (4.976733744101 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-17/128 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (145:ℝ) = Real.log (145/128) + 7 * Real.log 2 := by
    have h1 : Real.log ((145:ℝ)/128) = Real.log 145 - Real.log 128 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (128:ℝ) = 7 * Real.log 2 := by
      rw [show (128:ℝ) = 2^7 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  constructor <;> linarith [hle.1, hle.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `x^(1-c) = x * exp (-(c log x))`: the shape every power bound is taken in. -/
theorem rpow_one_sub_eq (x : ℝ) (hx : 0 < x) (c : ℝ) :
    x ^ (1 - c) = x * Real.exp (-(c * Real.log x)) := by
  rw [Real.rpow_def_of_pos hx]
  rw [show Real.log x * (1 - c) = Real.log x + -(c * Real.log x) by ring]
  rw [Real.exp_add, Real.exp_log hx]


/-- `1^(1-κ) = 1`. -/
theorem pow_1_bounds : (1:ℝ) ≤ (1:ℝ)^(1 - (kappa:ℝ)) ∧ (1:ℝ)^(1 - (kappa:ℝ)) ≤ (1:ℝ) := by
  simp

/-- `2^(1-κ)` to twelve decimal places. -/
theorem pow_2_bounds : (1.995448418119 : ℝ) ≤ (2:ℝ)^(1 - (kappa:ℝ)) ∧
    (2:ℝ)^(1 - (kappa:ℝ)) ≤ (1.995448418127 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_2_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (2:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (0.693147180300:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (0.693147180800:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (0.693147180300:ℝ))) ^ m / (m.factorial : ℝ)) = ((124715526132769009278938968647701220648254864619008784687945229628022095867749079455637671570133 : ℝ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (0.693147180800:ℝ))) ^ m / (m.factorial : ℝ)) = ((348451154676910597194166616113760457676502877757373829858953004677874275929805818637851 : ℝ) / 349245965480804443359375000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (0.693147180300:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (0.693147180800:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (0.693147180300:ℝ))) ≤ ((124715526132769009278938968647701220648254864619008784687945229628022095867749079455637671570133 : ℝ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((348451154676910597194166616113760457676502877757373829858953004677874275929805818637851 : ℝ) / 349245965480804443359375000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (0.693147180800:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 2)) ≤ Real.exp (-((kappa:ℝ) * (0.693147180300:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (0.693147180800:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 2)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `3^(1-κ)` to twelve decimal places. -/
theorem pow_3_bounds : (2.989186075197 : ℝ) ≤ (3:ℝ)^(1 - (kappa:ℝ)) ∧
    (3:ℝ)^(1 - (kappa:ℝ)) ≤ (2.989186075214 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_3_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (3:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (1.098612288143:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (1.098612289154:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (1.098612288143:ℝ))) ^ m / (m.factorial : ℝ)) = ((3736482594012690346384347407165583471876153294039540212903778477330002052026751452453258991964400442312499 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (1.098612289154:ℝ))) ^ m / (m.factorial : ℝ)) = ((116765081062508542975328809674511155446730282280707049251228049228919688472604386628438783261985322918301 : ℝ) / 117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (1.098612288143:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (1.098612289154:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (1.098612288143:ℝ))) ≤ ((3736482594012690346384347407165583471876153294039540212903778477330002052026751452453258991964400442312499 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((116765081062508542975328809674511155446730282280707049251228049228919688472604386628438783261985322918301 : ℝ) / 117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (1.098612289154:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 3)) ≤ Real.exp (-((kappa:ℝ) * (1.098612288143:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (1.098612289154:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 3)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `4^(1-κ)` to twelve decimal places. -/
theorem pow_4_bounds : (3.981814389377 : ℝ) ≤ (4:ℝ)^(1 - (kappa:ℝ)) ∧
    (4:ℝ)^(1 - (kappa:ℝ)) ≤ (3.981814389399 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_4_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (4:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (1.386294360600:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (1.386294361600:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (1.386294360600:ℝ))) ^ m / (m.factorial : ℝ)) = ((3888490614643347371743082445003551190306726407023877431797906944455810822411579455637671570133 : ℝ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (1.386294361600:ℝ))) ^ m / (m.factorial : ℝ)) = ((10864317271757589230278232936261082257718032682107453414955302568014705617305818637851 : ℝ) / 10913936421275138854980468750000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (1.386294360600:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (1.386294361600:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (1.386294360600:ℝ))) ≤ ((3888490614643347371743082445003551190306726407023877431797906944455810822411579455637671570133 : ℝ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((10864317271757589230278232936261082257718032682107453414955302568014705617305818637851 : ℝ) / 10913936421275138854980468750000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (1.386294361600:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 4)) ≤ Real.exp (-((kappa:ℝ) * (1.386294360600:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (1.386294361600:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 4)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `5^(1-κ)` to twelve decimal places. -/
theorem pow_5_bounds : (4.973618618747 : ℝ) ≤ (5:ℝ)^(1 - (kappa:ℝ)) ∧
    (5:ℝ)^(1 - (kappa:ℝ)) ≤ (4.973618618774 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_5_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (5:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (1.609437911909:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (1.609437912919:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (1.609437911909:ℝ))) ^ m / (m.factorial : ℝ)) = ((3730213964076591556279187155924384935582804373307620566257123183364963582796735976274107848407805612599457 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (1.609437912919:ℝ))) ^ m / (m.factorial : ℝ)) = ((3730213964064207678101062876507244629669427714888321690719912848571257205640503772766986698429103936090107 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (1.609437911909:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (1.609437912919:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (1.609437911909:ℝ))) ≤ ((3730213964076591556279187155924384935582804373307620566257123183364963582796735976274107848407805612599457 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((3730213964064207678101062876507244629669427714888321690719912848571257205640503772766986698429103936090107 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (1.609437912919:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 5)) ≤ Real.exp (-((kappa:ℝ) * (1.609437911909:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (1.609437912919:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 5)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `6^(1-κ)` to twelve decimal places. -/
theorem pow_6_bounds : (5.964766625221 : ℝ) ≤ (6:ℝ)^(1 - (kappa:ℝ)) ∧
    (6:ℝ)^(1 - (kappa:ℝ)) ≤ (5.964766625264 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_6_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (6:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (1.791759468443:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (1.791759469954:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (1.791759468443:ℝ))) ^ m / (m.factorial : ℝ)) = ((3727979140785809550418744288507786035310823049733667996510041567755351460561910077363903430995082926651999 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (1.791759469954:ℝ))) ^ m / (m.factorial : ℝ)) = ((116499348148977933683177518709120204146680931580287687518415728749228732803079267676692405620549745494301 : ℝ) / 117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (1.791759468443:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (1.791759469954:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (1.791759468443:ℝ))) ≤ ((3727979140785809550418744288507786035310823049733667996510041567755351460561910077363903430995082926651999 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((116499348148977933683177518709120204146680931580287687518415728749228732803079267676692405620549745494301 : ℝ) / 117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (1.791759469954:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 6)) ≤ Real.exp (-((kappa:ℝ) * (1.791759468443:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (1.791759469954:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 6)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `7^(1-κ)` to twelve decimal places. -/
theorem pow_7_bounds : (6.955369249178 : ℝ) ≤ (7:ℝ)^(1 - (kappa:ℝ)) ∧
    (7:ℝ)^(1 - (kappa:ℝ)) ≤ (6.955369249227 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_7_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (7:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (1.945910148275:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (1.945910149776:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (1.945910148275:ℝ))) ^ m / (m.factorial : ℝ)) = ((381551684528639872328001185981166829109251429022246496295998997619572297031103218633382423042380143 : ℝ) / 384000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (1.945910149776:ℝ))) ^ m / (m.factorial : ℝ)) = ((1184492323941108365757772878104200599623159589425844213466146302225867943863498281108479871594627031 : ℝ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (1.945910148275:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (1.945910149776:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (1.945910148275:ℝ))) ≤ ((381551684528639872328001185981166829109251429022246496295998997619572297031103218633382423042380143 : ℝ) / 384000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((1184492323941108365757772878104200599623159589425844213466146302225867943863498281108479871594627031 : ℝ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (1.945910149776:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 7)) ≤ Real.exp (-((kappa:ℝ) * (1.945910148275:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (1.945910149776:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 7)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `8^(1-κ)` to twelve decimal places. -/
theorem pow_8_bounds : (7.945505224535 : ℝ) ≤ (8:ℝ)^(1 - (kappa:ℝ)) ∧
    (8:ℝ)^(1 - (kappa:ℝ)) ≤ (7.945505224591 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_8_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (8:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (2.079441540900:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (2.079441542400:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (2.079441540900:ℝ))) ^ m / (m.factorial : ℝ)) = ((124148519134100314476574539041129150378390801374087940654458250133892941173676307719954191542319 : ℝ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (2.079441542400:ℝ))) ^ m / (m.factorial : ℝ)) = ((115622318474099224056924123343450007186916154779192592896879051042982756564271309665931 : ℝ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (2.079441540900:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (2.079441542400:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (2.079441540900:ℝ))) ≤ ((124148519134100314476574539041129150378390801374087940654458250133892941173676307719954191542319 : ℝ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((115622318474099224056924123343450007186916154779192592896879051042982756564271309665931 : ℝ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (2.079441542400:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 8)) ≤ Real.exp (-((kappa:ℝ) * (2.079441540900:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (2.079441542400:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 8)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `9^(1-κ)` to twelve decimal places. -/
theorem pow_9_bounds : (8.935233392169 : ℝ) ≤ (9:ℝ)^(1 - (kappa:ℝ)) ∧
    (9:ℝ)^(1 - (kappa:ℝ)) ≤ (8.935233392232 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_9_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (9:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (2.197224576556:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (2.197224578057:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (2.197224576556:ℝ))) ^ m / (m.factorial : ℝ)) = ((3635755774830054713823631678175516797715504927989843641302817169095437746075069129573648663048839971407 : ℝ) / 3662109375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (2.197224578057:ℝ))) ^ m / (m.factorial : ℝ)) = ((3723013913407607391073146539607368743926472086929494898447342794454939866173264347450860523142480974470501 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (2.197224576556:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (2.197224578057:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (2.197224576556:ℝ))) ≤ ((3635755774830054713823631678175516797715504927989843641302817169095437746075069129573648663048839971407 : ℝ) / 3662109375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((3723013913407607391073146539607368743926472086929494898447342794454939866173264347450860523142480974470501 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (2.197224578057:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 9)) ≤ Real.exp (-((kappa:ℝ) * (2.197224576556:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (2.197224578057:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 9)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `16^(1-κ)` to twelve decimal places. -/
theorem pow_16_bounds : (15.854845831471 : ℝ) ≤ (16:ℝ)^(1 - (kappa:ℝ)) ∧
    (16:ℝ)^(1 - (kappa:ℝ)) ≤ (15.854845831608 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_16_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (16:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (2.772588721200:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (2.772588723200:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (2.772588721200:ℝ))) ^ m / (m.factorial : ℝ)) = ((120962874081355085442203666050106625374535631851307223692995602672668299742829455637671570133 : ℝ) / 122070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (2.772588723200:ℝ))) ^ m / (m.factorial : ℝ)) = ((337966365964784860949128559472452561476545739162932490319732763084920461055818637851 : ℝ) / 341060513164848089218139648437500000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (2.772588721200:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (2.772588723200:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (2.772588721200:ℝ))) ≤ ((120962874081355085442203666050106625374535631851307223692995602672668299742829455637671570133 : ℝ) / 122070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((337966365964784860949128559472452561476545739162932490319732763084920461055818637851 : ℝ) / 341060513164848089218139648437500000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (2.772588723200:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 16)) ≤ Real.exp (-((kappa:ℝ) * (2.772588721200:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (2.772588723200:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 16)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `17^(1-κ)` to twelve decimal places. -/
theorem pow_17_bounds : (16.842417106008 : ℝ) ≤ (17:ℝ)^(1 - (kappa:ℝ)) ∧
    (17:ℝ)^(1 - (kappa:ℝ)) ≤ (16.842417106153 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_17_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (17:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (2.833213343016:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (2.833213345017:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (2.833213343016:ℝ))) ^ m / (m.factorial : ℝ)) = ((37793366165465969582697418123390545572750546886457990092303529564737588040090489723515727469949544267 : ℝ) / 38146972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (2.833213345017:ℝ))) ^ m / (m.factorial : ℝ)) = ((1238413022501843458719362915364997476806893675106015252912304040190568655414676377840343924381244690496967 : ℝ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (2.833213343016:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (2.833213345017:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (2.833213343016:ℝ))) ≤ ((37793366165465969582697418123390545572750546886457990092303529564737588040090489723515727469949544267 : ℝ) / 38146972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((1238413022501843458719362915364997476806893675106015252912304040190568655414676377840343924381244690496967 : ℝ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (2.833213345017:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 17)) ≤ Real.exp (-((kappa:ℝ) * (2.833213343016:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (2.833213345017:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 17)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `24^(1-κ)` to twelve decimal places. -/
theorem pow_24_bounds : (23.750593577611 : ℝ) ≤ (24:ℝ)^(1 - (kappa:ℝ)) ∧
    (24:ℝ)^(1 - (kappa:ℝ)) ≤ (23.750593577856 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_24_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (24:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (3.178053829043:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (3.178053831554:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (3.178053829043:ℝ))) ^ m / (m.factorial : ℝ)) = ((3711030246536131898819526106440999592984872194926856220333558993168658511214958938428808820261736370730999 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (3.178053831554:ℝ))) ^ m / (m.factorial : ℝ)) = ((115969695203296943674704014600457087014911417975366766789648168957431341533762335924543782566770533046301 : ℝ) / 117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (3.178053829043:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (3.178053831554:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (3.178053829043:ℝ))) ≤ ((3711030246536131898819526106440999592984872194926856220333558993168658511214958938428808820261736370730999 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((115969695203296943674704014600457087014911417975366766789648168957431341533762335924543782566770533046301 : ℝ) / 117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (3.178053831554:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 24)) ≤ Real.exp (-((kappa:ℝ) * (3.178053829043:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (3.178053831554:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 24)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `25^(1-κ)` to twelve decimal places. -/
theorem pow_25_bounds : (24.736882164755 : ℝ) ≤ (25:ℝ)^(1 - (kappa:ℝ)) ∧
    (25:ℝ)^(1 - (kappa:ℝ)) ≤ (24.736882165009 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_25_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (25:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (3.218875823568:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (3.218875826069:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (3.218875823568:ℝ))) ^ m / (m.factorial : ℝ)) = ((1179546459435645790869326975960463775923606563712625856637086218816104623868053585396227405608962483 : ℝ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (3.218875826069:ℝ))) ^ m / (m.factorial : ℝ)) = ((3710532324717071536600934065102161056368457824527717630138084902202302443457570693664528461547907067099857 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (3.218875823568:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (3.218875826069:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (3.218875823568:ℝ))) ≤ ((1179546459435645790869326975960463775923606563712625856637086218816104623868053585396227405608962483 : ℝ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((3710532324717071536600934065102161056368457824527717630138084902202302443457570693664528461547907067099857 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (3.218875826069:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 25)) ≤ Real.exp (-((kappa:ℝ) * (3.218875823568:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (3.218875826069:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 25)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `32^(1-κ)` to twelve decimal places. -/
theorem pow_32_bounds : (31.637527033961 : ℝ) ≤ (32:ℝ)^(1 - (kappa:ℝ)) ∧
    (32:ℝ)^(1 - (kappa:ℝ)) ≤ (31.637527034286 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_32_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (32:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (3.465735901500:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (3.465735904000:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (3.465735901500:ℝ))) ^ m / (m.factorial : ℝ)) = ((39546908792817065871952923257228906281447743282383855669513334316039795209079455637671570133 : ℝ) / 40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (3.465735904000:ℝ))) ^ m / (m.factorial : ℝ)) = ((110492786744121707318742622592761127477100541899121689181681302098963429805818637851 : ℝ) / 111758708953857421875000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (3.465735901500:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (3.465735904000:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (3.465735901500:ℝ))) ≤ ((39546908792817065871952923257228906281447743282383855669513334316039795209079455637671570133 : ℝ) / 40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((110492786744121707318742622592761127477100541899121689181681302098963429805818637851 : ℝ) / 111758708953857421875000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (3.465735904000:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 32)) ≤ Real.exp (-((kappa:ℝ) * (3.465735901500:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (3.465735904000:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 32)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `33^(1-κ)` to twelve decimal places. -/
theorem pow_33_bounds : (32.622899882583 : ℝ) ≤ (33:ℝ)^(1 - (kappa:ℝ)) ∧
    (33:ℝ)^(1 - (kappa:ℝ)) ≤ (32.622899882918 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_33_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (33:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (3.496507560166:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (3.496507562667:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (3.496507560166:ℝ))) ^ m / (m.factorial : ℝ)) = ((115848366061381351630082931384612844488216274867547739050951374955788416443862990568511131287743323260599 : ℝ) / 117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (3.496507562667:ℝ))) ^ m / (m.factorial : ℝ)) = ((1235715904644575816875540286229186918495528005643787430364621979944561191390780401783263703890119916647717 : ℝ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (3.496507560166:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (3.496507562667:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (3.496507560166:ℝ))) ≤ ((115848366061381351630082931384612844488216274867547739050951374955788416443862990568511131287743323260599 : ℝ) / 117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((1235715904644575816875540286229186918495528005643787430364621979944561191390780401783263703890119916647717 : ℝ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (3.496507562667:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 33)) ≤ Real.exp (-((kappa:ℝ) * (3.496507560166:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (3.496507562667:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 33)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `56^(1-κ)` to twelve decimal places. -/
theorem pow_56_bounds : (55.263922707975 : ℝ) ≤ (56:ℝ)^(1 - (kappa:ℝ)) ∧
    (56:ℝ)^(1 - (kappa:ℝ)) ≤ (55.263922708633 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_56_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (56:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (4.025351689175:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (4.025351692176:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (4.025351689175:ℝ))) ^ m / (m.factorial : ℝ)) = ((378952612858813666826463657534611098741579804993342642360768481547694641720185674053686792351941651 : ℝ) / 384000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (4.025351692176:ℝ))) ^ m / (m.factorial : ℝ)) = ((1176423743538172150566289165270245908692720981370592652350960036311302888301512747932033822928249031 : ℝ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (4.025351689175:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (4.025351692176:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (4.025351689175:ℝ))) ≤ ((378952612858813666826463657534611098741579804993342642360768481547694641720185674053686792351941651 : ℝ) / 384000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((1176423743538172150566289165270245908692720981370592652350960036311302888301512747932033822928249031 : ℝ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (4.025351692176:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 56)) ≤ Real.exp (-((kappa:ℝ) * (4.025351689175:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (4.025351692176:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 56)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `57^(1-κ)` to twelve decimal places. -/
theorem pow_57_bounds : (56.247505965402 : ℝ) ≤ (57:ℝ)^(1 - (kappa:ℝ)) ∧
    (57:ℝ)^(1 - (kappa:ℝ)) ≤ (56.247505966072 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_57_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (57:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (4.043051266274:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (4.043051269275:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (4.043051266274:ℝ))) ^ m / (m.factorial : ℝ)) = ((115640431673548633137187613516289744500212793110793212920211611899916858417723446402096057118543802698701 : ℝ) / 117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (4.043051269275:ℝ))) ^ m / (m.factorial : ℝ)) = ((126310188834715421760815514854425290705610602101284471465881284551655783852540979898731359252223581 : ℝ) / 128000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (4.043051266274:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (4.043051269275:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (4.043051266274:ℝ))) ≤ ((115640431673548633137187613516289744500212793110793212920211611899916858417723446402096057118543802698701 : ℝ) / 117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((126310188834715421760815514854425290705610602101284471465881284551655783852540979898731359252223581 : ℝ) / 128000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (4.043051269275:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 57)) ≤ Real.exp (-((kappa:ℝ) * (4.043051266274:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (4.043051269275:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 57)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `73^(1-κ)` to twelve decimal places. -/
theorem pow_73_bounds : (71.977721022756 : ℝ) ≤ (73:ℝ)^(1 - (kappa:ℝ)) ∧
    (73:ℝ)^(1 - (kappa:ℝ)) ≤ (71.977721023613 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_73_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (73:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (4.290459439588:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (4.290459442589:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (4.290459439588:ℝ))) ^ m / (m.factorial : ℝ)) = ((3610825848649829612388265208342353928857898973272739655473811838751295267165830736265674526801749670101 : ℝ) / 3662109375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (4.290459442589:ℝ))) ^ m / (m.factorial : ℝ)) = ((3697485668980952307921853707086116719377065739391732544674960560028923947767155744538729927638325306445657 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (4.290459439588:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (4.290459442589:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (4.290459439588:ℝ))) ≤ ((3610825848649829612388265208342353928857898973272739655473811838751295267165830736265674526801749670101 : ℝ) / 3662109375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((3697485668980952307921853707086116719377065739391732544674960560028923947767155744538729927638325306445657 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (4.290459442589:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 73)) ≤ Real.exp (-((kappa:ℝ) * (4.290459439588:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (4.290459442589:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 73)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

/-- `145^(1-κ)` to twelve decimal places. -/
theorem pow_145_bounds : (142.647299842062 : ℝ) ≤ (145:ℝ)^(1 - (kappa:ℝ)) ∧
    (145:ℝ)^(1 - (kappa:ℝ)) ≤ (142.647299843995 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_145_bounds
  have hk : (0:ℝ) < (kappa:ℝ) := by norm_num [kappa]
  rw [rpow_one_sub_eq (145:ℝ) (by norm_num) (kappa:ℝ)]
  have hup := Real.exp_bound (x := -((kappa:ℝ) * (4.976733740600:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hdn := Real.exp_bound (x := -((kappa:ℝ) * (4.976733744101:ℝ))) (by norm_num [kappa]) (n := 6) (by norm_num)
  have hp1 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (4.976733740600:ℝ))) ^ m / (m.factorial : ℝ)) = ((11528607207207624937525751890917982795226188698813029491095825599655269371907370655629159648899 : ℝ) / 11718750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  have hp2 : (∑ m ∈ Finset.range 6, (-((kappa:ℝ) * (4.976733744101:ℝ))) ^ m / (m.factorial : ℝ)) = ((3689154306263985797220747163092126005422522160011205205898835420236978129630935109767175847729977221372193 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num [kappa]
  rw [hp1] at hup
  rw [hp2] at hdn
  have herr1 : |(-((kappa:ℝ) * (4.976733740600:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have herr2 : |(-((kappa:ℝ) * (4.976733744101:ℝ)))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1e-12 : ℝ) := by norm_num [kappa]
  have b1 : Real.exp (-((kappa:ℝ) * (4.976733740600:ℝ))) ≤ ((11528607207207624937525751890917982795226188698813029491095825599655269371907370655629159648899 : ℝ) / 11718750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) + 1e-12 := by
    have := (abs_le.mp hup).2; linarith
  have b2 : ((3689154306263985797220747163092126005422522160011205205898835420236978129630935109767175847729977221372193 : ℝ) / 3750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) - 1e-12 ≤ Real.exp (-((kappa:ℝ) * (4.976733744101:ℝ))) := by
    have := (abs_le.mp hdn).1; linarith
  have m1 : Real.exp (-((kappa:ℝ) * Real.log 145)) ≤ Real.exp (-((kappa:ℝ) * (4.976733740600:ℝ))) := by
    apply Real.exp_le_exp.mpr; nlinarith [hlo, hk]
  have m2 : Real.exp (-((kappa:ℝ) * (4.976733744101:ℝ))) ≤ Real.exp (-((kappa:ℝ) * Real.log 145)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hhi, hk]
  constructor <;> linarith [m1, m2, b1, b2]

end
end Pr6453

/-- **The moment inequality at the claimed saving.** -/
theorem solution :
    Pr6453.moment Pr6453.paid (1 - (Pr6453.kappa : ℝ)) <
      Pr6453.moment Pr6453.targets (1 - (Pr6453.kappa : ℝ)) := by
  have h1 := Pr6453.pow_1_bounds
  have h2 := Pr6453.pow_2_bounds
  have h3 := Pr6453.pow_3_bounds
  have h4 := Pr6453.pow_4_bounds
  have h5 := Pr6453.pow_5_bounds
  have h6 := Pr6453.pow_6_bounds
  have h7 := Pr6453.pow_7_bounds
  have h8 := Pr6453.pow_8_bounds
  have h9 := Pr6453.pow_9_bounds
  have h16 := Pr6453.pow_16_bounds
  have h17 := Pr6453.pow_17_bounds
  have h24 := Pr6453.pow_24_bounds
  have h25 := Pr6453.pow_25_bounds
  have h32 := Pr6453.pow_32_bounds
  have h33 := Pr6453.pow_33_bounds
  have h56 := Pr6453.pow_56_bounds
  have h57 := Pr6453.pow_57_bounds
  have h73 := Pr6453.pow_73_bounds
  have h145 := Pr6453.pow_145_bounds
  simp only [Pr6453.moment, Pr6453.targets, Pr6453.paid, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.cast_ofNat, Nat.cast_one, Real.one_rpow, mul_one, add_zero]
  linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2,
    h7.1, h7.2, h8.1, h8.2, h9.1, h9.2, h16.1, h16.2, h17.1, h17.2, h24.1, h24.2,
    h25.1, h25.2, h32.1, h32.2, h33.1, h33.2, h56.1, h56.2, h57.1, h57.2, h73.1, h73.2,
    h145.1, h145.2]

