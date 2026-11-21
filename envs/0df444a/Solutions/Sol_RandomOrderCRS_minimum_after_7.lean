-- Prove2me | solution 1 for RandomOrderCRS.minimum_after_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:55:11.99111+00:00
-- url     : https://prove2.me/submissions/9dbc9be0-31e1-4216-84dd-b6068b26fab8

import Mathlib
import Definitions.Def_RandomOrderCRS_Attenuation

open Real

namespace Aux_RandomOrderCRS_minimum_after_7

def hor : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: l, y => a + y * hor l y

def horD : List ℝ → ℝ → ℝ
  | [], _ => 0
  | _ :: l, y => hor l y + y * horD l y

lemma hasDerivAt_hor (l : List ℝ) (y : ℝ) : HasDerivAt (hor l) (horD l y) y := by
  induction l with
  | nil =>
    show HasDerivAt (fun _ => (0:ℝ)) 0 y
    exact hasDerivAt_const y 0
  | cons a l ih =>
    show HasDerivAt (fun y => a + y * hor l y) (hor l y + y * horD l y) y
    have := (hasDerivAt_const y a).add ((hasDerivAt_id' y).mul ih)
    exact this.congr_deriv (by ring)

lemma continuous_hor (l : List ℝ) : Continuous (hor l) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_hor l y).continuousAt

lemma continuous_horD (l : List ℝ) : Continuous (horD l) := by
  induction l with
  | nil =>
    show Continuous (fun _ => (0:ℝ))
    exact continuous_const
  | cons a l ih =>
    show Continuous (fun y => hor l y + y * horD l y)
    exact (continuous_hor l).add (continuous_id.mul ih)

lemma integral_hor (l : List ℝ) (g : ℝ → ℝ)
    (hg : ∀ y, g y = exp (-2 * y) * (2 * hor l y - horD l y)) :
    ∫ y in (0:ℝ)..1, g y = hor l 0 - exp (-2) * hor l 1 := by
  have hderiv : ∀ y ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y => -exp (-2 * y) * hor l y) (g y) y := by
    intro y _
    have h1 : HasDerivAt (fun y => exp (-2 * y)) (exp (-2 * y) * (-2 * 1)) y :=
      ((hasDerivAt_id' y).const_mul (-2)).exp
    have := h1.fun_neg.fun_mul (hasDerivAt_hor l y)
    rw [hg]
    exact this.congr_deriv (by ring)
  have hcont : Continuous g := by
    have : g = fun y => exp (-2 * y) * (2 * hor l y - horD l y) := funext hg
    rw [this]
    exact (continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_const.mul (continuous_hor l)).sub (continuous_horD l))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
  simp only [mul_zero, mul_one, exp_zero]
  ring

lemma mb_lo (t d : ℝ) (j k : ℕ) (ht0 : 0 ≤ t) (hd0 : 0 ≤ d) : 0 ≤ t ^ j * d ^ k := by
  positivity

lemma mb_hi (t d : ℝ) (j k : ℕ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hk : k ≠ 0) : t ^ j * d ^ k ≤ d := by
  have h1 : t ^ j ≤ 1 := pow_le_one₀ ht0 ht1
  have h2 : d ^ k ≤ d := pow_le_of_le_one hd0 hd1 hk
  have h3 : 0 ≤ d ^ k := pow_nonneg hd0 k
  calc t ^ j * d ^ k ≤ 1 * d ^ k := mul_le_mul_of_nonneg_right h1 h3
    _ ≤ d := by rw [one_mul]; exact h2

noncomputable def pexpr (t A y : ℝ) : ℝ :=
  (1 + 2 * y * t + (2 * y * t) ^ 2 / 2 + (2 * y * t) ^ 3 / 6 + (2 * y * t) ^ 4 / 24) *
    (1 + A * (1 - t) * y ^ 2)

noncomputable def lt (t A : ℝ) : List ℝ := [-15*A*t^5/4 + 5*A*t^4/4 + A*t^3 + 3*A*t^2/4 + A*t/2 + A/4 + t^4/2 + t^3/2 + t^2/2 + t/2 + 1/2, -15*A*t^5/2 + 5*A*t^4/2 + 2*A*t^3 + 3*A*t^2/2 + A*t + A/2 + t^4 + t^3 + t^2 + t, -15*A*t^5/2 + 5*A*t^4/2 + 2*A*t^3 + 3*A*t^2/2 + A*t + A/2 + t^4 + t^3 + t^2, -5*A*t^5 + 5*A*t^4/3 + 4*A*t^3/3 + A*t^2 + A*t + 2*t^4/3 + 2*t^3/3, -5*A*t^5/2 + 5*A*t^4/6 + 2*A*t^3/3 + A*t^2 + t^4/3, -A*t^5 + A*t^4/3 + 2*A*t^3/3, -A*t^5/3 + A*t^4/3]

set_option maxHeartbeats 1600000 in
lemma keyD1' (d t : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 10000) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 ≤ (-15) * t^6 * d^6 + (-47319/500) * t^6 * d^5 + (-205362587/3000000) * t^6 * d^4 + (73855768361/3750000000) * t^6 * d^3 + (1042240597358053/75000000000000) * t^6 * d^2 + (-1016448771548825559/312500000000000000) * t^6 * d^1 + (-63468789280568949123/3125000000000000000000) * t^6 + (5) * t^5 * d^6 + (773/500) * t^5 * d^5 + (-521402471/3000000) * t^5 * d^4 + (-237779855929/1250000000) * t^5 * d^3 + (-1839491531899351/75000000000000) * t^5 * d^2 + (7894636725010866853/312500000000000000) * t^5 * d^1 + (550703478838354453041/3125000000000000000000) * t^5 + (4) * t^4 * d^6 + (22023/625) * t^4 * d^5 + (262200029/3750000) * t^4 * d^4 + (-51957384679/1562500000) * t^4 * d^3 + (-10231229029294351/93750000000000) * t^4 * d^2 + (-64042641997953580691/1171875000000000000) * t^4 * d^1 + (-4235090724273241638377/11718750000000000000000) * t^4 + (3) * t^3 * d^6 + (67319/2500) * t^3 * d^5 + (362427529/5000000) * t^3 * d^4 + (1729402091639/18750000000) * t^3 * d^3 + (22816778765681947/375000000000000) * t^3 * d^2 + (67336342095544776677/4687500000000000000) * t^3 * d^1 + (-5484429579494564032631/46875000000000000000000) * t^3 + (2) * t^2 * d^6 + (23273/1250) * t^2 * d^5 + (138460843/2500000) * t^2 * d^4 + (237157966571/3125000000) * t^2 * d^3 + (10580813139270649/187500000000000) * t^2 * d^2 + (11887895778908979353/781250000000000000) * t^2 * d^1 + (-4318022980306818255877/23437500000000000000000) * t^2 + (1) * t^1 * d^6 + (25773/2500) * t^1 * d^5 + (191415843/5000000) * t^1 * d^4 + (388831169071/6250000000) * t^1 * d^3 + (6970357930466883/125000000000000) * t^1 * d^2 + (31231692917120991853/1562500000000000000) * t^1 * d^1 + (4478995993089097003041/15625000000000000000000) * t^1 + (2) * d^5 + (7591/500) * d^4 + (44123281/1250000) * d^3 + (290482826071/6250000000) * d^2 + (2248378752204961/62500000000000) * d^1 + (2003881103153858951/1562500000000000000) := by
  have hd1' : d ≤ 1 := by linarith
  linarith [mb_lo t d 6 6 ht0 hd0, mb_hi t d 6 6 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 6 5 ht0 hd0, mb_hi t d 6 5 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 6 4 ht0 hd0, mb_hi t d 6 4 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 6 3 ht0 hd0, mb_hi t d 6 3 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 6 2 ht0 hd0, mb_hi t d 6 2 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 6 1 ht0 hd0, mb_hi t d 6 1 ht0 ht1 hd0 hd1' (by norm_num),
      pow_nonneg ht0 6, pow_le_one₀ (n := 6) ht0 ht1,
      mb_lo t d 5 6 ht0 hd0, mb_hi t d 5 6 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 5 5 ht0 hd0, mb_hi t d 5 5 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 5 4 ht0 hd0, mb_hi t d 5 4 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 5 3 ht0 hd0, mb_hi t d 5 3 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 5 2 ht0 hd0, mb_hi t d 5 2 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 5 1 ht0 hd0, mb_hi t d 5 1 ht0 ht1 hd0 hd1' (by norm_num),
      pow_nonneg ht0 5, pow_le_one₀ (n := 5) ht0 ht1,
      mb_lo t d 4 6 ht0 hd0, mb_hi t d 4 6 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 4 5 ht0 hd0, mb_hi t d 4 5 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 4 4 ht0 hd0, mb_hi t d 4 4 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 4 3 ht0 hd0, mb_hi t d 4 3 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 4 2 ht0 hd0, mb_hi t d 4 2 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 4 1 ht0 hd0, mb_hi t d 4 1 ht0 ht1 hd0 hd1' (by norm_num),
      pow_nonneg ht0 4, pow_le_one₀ (n := 4) ht0 ht1,
      mb_lo t d 3 6 ht0 hd0, mb_hi t d 3 6 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 3 5 ht0 hd0, mb_hi t d 3 5 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 3 4 ht0 hd0, mb_hi t d 3 4 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 3 3 ht0 hd0, mb_hi t d 3 3 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 3 2 ht0 hd0, mb_hi t d 3 2 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 3 1 ht0 hd0, mb_hi t d 3 1 ht0 ht1 hd0 hd1' (by norm_num),
      pow_nonneg ht0 3, pow_le_one₀ (n := 3) ht0 ht1,
      mb_lo t d 2 6 ht0 hd0, mb_hi t d 2 6 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 2 5 ht0 hd0, mb_hi t d 2 5 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 2 4 ht0 hd0, mb_hi t d 2 4 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 2 3 ht0 hd0, mb_hi t d 2 3 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 2 2 ht0 hd0, mb_hi t d 2 2 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 2 1 ht0 hd0, mb_hi t d 2 1 ht0 ht1 hd0 hd1' (by norm_num),
      pow_nonneg ht0 2, pow_le_one₀ (n := 2) ht0 ht1,
      mb_lo t d 1 6 ht0 hd0, mb_hi t d 1 6 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 1 5 ht0 hd0, mb_hi t d 1 5 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 1 4 ht0 hd0, mb_hi t d 1 4 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 1 3 ht0 hd0, mb_hi t d 1 3 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 1 2 ht0 hd0, mb_hi t d 1 2 ht0 ht1 hd0 hd1' (by norm_num),
      mb_lo t d 1 1 ht0 hd0, mb_hi t d 1 1 ht0 ht1 hd0 hd1' (by norm_num),
      pow_nonneg ht0 1, pow_le_one₀ (n := 1) ht0 ht1,
      pow_nonneg hd0 5, pow_le_of_le_one hd0 hd1' (by norm_num : (5:ℕ) ≠ 0),
      pow_nonneg hd0 4, pow_le_of_le_one hd0 hd1' (by norm_num : (4:ℕ) ≠ 0),
      pow_nonneg hd0 3, pow_le_of_le_one hd0 hd1' (by norm_num : (3:ℕ) ≠ 0),
      pow_nonneg hd0 2, pow_le_of_le_one hd0 hd1' (by norm_num : (2:ℕ) ≠ 0),
      pow_nonneg hd0 1, pow_le_of_le_one hd0 hd1' (by norm_num : (1:ℕ) ≠ 0)]

set_option maxHeartbeats 1600000 in
lemma keyD1 (E t : ℝ) (h1 : 27182 / 10000 < E) (h2 : E < 27183 / 10000) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 ≤ -15*E^6*t^6 + 5*E^6*t^5 + 4*E^6*t^4 + 3*E^6*t^3 + 2*E^6*t^2 + E^6*t + 150*E^5*t^6 - 80*E^5*t^5 - 30*E^5*t^4 - 22*E^5*t^3 - 14*E^5*t^2 - 6*E^5*t + 2*E^5 - 1334*E^4*t^6/3 + 1078*E^4*t^5/3 + 103*E^4*t^4/3 + 39*E^4*t^3 + 24*E^4*t^2 + 9*E^4*t - 12*E^4 - 610*E^3*t^6/3 - 584*E^3*t^5/3 + 610*E^3*t^4/3 + 266*E^3*t^3/3 + 46*E^3*t^2 + 6*E^3*t + 18*E^3 + 10627*E^2*t^6/3 - 7183*E^2*t^5/3 - 1619*E^2*t^4/3 - 1288*E^2*t^3/3 - 626*E^2*t^2/3 - 6*E^2*t + 30*E^2 - 6620*E*t^6 + 17624*E*t^5/3 + 724*E*t^4/3 + 584*E*t^3 + 728*E*t^2/3 - 56*E*t - 108*E + 3972*t^6 - 4130*t^5 + 634*t^4/3 - 812*t^3/3 - 244*t^2/3 + 72*t + 70 := by
  have h := keyD1' (E - 27182 / 10000) t (by linarith) (by linarith) ht0 ht1
  have hexp : -15*E^6*t^6 + 5*E^6*t^5 + 4*E^6*t^4 + 3*E^6*t^3 + 2*E^6*t^2 + E^6*t + 150*E^5*t^6 - 80*E^5*t^5 - 30*E^5*t^4 - 22*E^5*t^3 - 14*E^5*t^2 - 6*E^5*t + 2*E^5 - 1334*E^4*t^6/3 + 1078*E^4*t^5/3 + 103*E^4*t^4/3 + 39*E^4*t^3 + 24*E^4*t^2 + 9*E^4*t - 12*E^4 - 610*E^3*t^6/3 - 584*E^3*t^5/3 + 610*E^3*t^4/3 + 266*E^3*t^3/3 + 46*E^3*t^2 + 6*E^3*t + 18*E^3 + 10627*E^2*t^6/3 - 7183*E^2*t^5/3 - 1619*E^2*t^4/3 - 1288*E^2*t^3/3 - 626*E^2*t^2/3 - 6*E^2*t + 30*E^2 - 6620*E*t^6 + 17624*E*t^5/3 + 724*E*t^4/3 + 584*E*t^3 + 728*E*t^2/3 - 56*E*t - 108*E + 3972*t^6 - 4130*t^5 + 634*t^4/3 - 812*t^3/3 - 244*t^2/3 + 72*t + 70 = (-15) * t^6 * (E - 27182/10000)^6 + (-47319/500) * t^6 * (E - 27182/10000)^5 + (-205362587/3000000) * t^6 * (E - 27182/10000)^4 + (73855768361/3750000000) * t^6 * (E - 27182/10000)^3 + (1042240597358053/75000000000000) * t^6 * (E - 27182/10000)^2 + (-1016448771548825559/312500000000000000) * t^6 * (E - 27182/10000)^1 + (-63468789280568949123/3125000000000000000000) * t^6 + (5) * t^5 * (E - 27182/10000)^6 + (773/500) * t^5 * (E - 27182/10000)^5 + (-521402471/3000000) * t^5 * (E - 27182/10000)^4 + (-237779855929/1250000000) * t^5 * (E - 27182/10000)^3 + (-1839491531899351/75000000000000) * t^5 * (E - 27182/10000)^2 + (7894636725010866853/312500000000000000) * t^5 * (E - 27182/10000)^1 + (550703478838354453041/3125000000000000000000) * t^5 + (4) * t^4 * (E - 27182/10000)^6 + (22023/625) * t^4 * (E - 27182/10000)^5 + (262200029/3750000) * t^4 * (E - 27182/10000)^4 + (-51957384679/1562500000) * t^4 * (E - 27182/10000)^3 + (-10231229029294351/93750000000000) * t^4 * (E - 27182/10000)^2 + (-64042641997953580691/1171875000000000000) * t^4 * (E - 27182/10000)^1 + (-4235090724273241638377/11718750000000000000000) * t^4 + (3) * t^3 * (E - 27182/10000)^6 + (67319/2500) * t^3 * (E - 27182/10000)^5 + (362427529/5000000) * t^3 * (E - 27182/10000)^4 + (1729402091639/18750000000) * t^3 * (E - 27182/10000)^3 + (22816778765681947/375000000000000) * t^3 * (E - 27182/10000)^2 + (67336342095544776677/4687500000000000000) * t^3 * (E - 27182/10000)^1 + (-5484429579494564032631/46875000000000000000000) * t^3 + (2) * t^2 * (E - 27182/10000)^6 + (23273/1250) * t^2 * (E - 27182/10000)^5 + (138460843/2500000) * t^2 * (E - 27182/10000)^4 + (237157966571/3125000000) * t^2 * (E - 27182/10000)^3 + (10580813139270649/187500000000000) * t^2 * (E - 27182/10000)^2 + (11887895778908979353/781250000000000000) * t^2 * (E - 27182/10000)^1 + (-4318022980306818255877/23437500000000000000000) * t^2 + (1) * t^1 * (E - 27182/10000)^6 + (25773/2500) * t^1 * (E - 27182/10000)^5 + (191415843/5000000) * t^1 * (E - 27182/10000)^4 + (388831169071/6250000000) * t^1 * (E - 27182/10000)^3 + (6970357930466883/125000000000000) * t^1 * (E - 27182/10000)^2 + (31231692917120991853/1562500000000000000) * t^1 * (E - 27182/10000)^1 + (4478995993089097003041/15625000000000000000000) * t^1 + (2) * (E - 27182/10000)^5 + (7591/500) * (E - 27182/10000)^4 + (44123281/1250000) * (E - 27182/10000)^3 + (290482826071/6250000000) * (E - 27182/10000)^2 + (2248378752204961/62500000000000) * (E - 27182/10000)^1 + (2003881103153858951/1562500000000000000) := by ring
  rw [hexp]
  exact h

set_option maxHeartbeats 1600000 in
lemma alg (E X t : ℝ) (hX : X * E ^ 2 = 1) (h1 : 27182 / 10000 < E) (h2 : E < 27183 / 10000)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (E ^ 2 - 4 * E ^ 3 + E ^ 4 + 20 * E - 22) / (4 * E ^ 2) ≤
      (1 - (3 - E) * t) ^ 2 * (hor (lt t ((E - 2) ^ 2)) 0 - X * hor (lt t ((E - 2) ^ 2)) 1) := by
  have hE : 0 < E := by linarith
  rw [div_le_iff₀ (mul_pos (by norm_num) (pow_pos hE 2))]
  have hD := keyD1 E t h1 h2 ht0 ht1
  have h0 : hor (lt t ((E - 2) ^ 2)) 0 = -15*(E - 2)^2*t^5/4 + 5*(E - 2)^2*t^4/4 + (E - 2)^2*t^3 + 3*(E - 2)^2*t^2/4 + (E - 2)^2*t/2 + (E - 2)^2/4 + t^4/2 + t^3/2 + t^2/2 + t/2 + 1/2 := by simp only [lt, hor]; ring
  have h1' : hor (lt t ((E - 2) ^ 2)) 1 = -331*(E - 2)^2*t^5/12 + 113*(E - 2)^2*t^4/12 + 23*(E - 2)^2*t^3/3 + 23*(E - 2)^2*t^2/4 + 7*(E - 2)^2*t/2 + 5*(E - 2)^2/4 + 7*t^4/2 + 19*t^3/6 + 5*t^2/2 + 3*t/2 + 1/2 := by simp only [lt, hor]; ring
  rw [h0, h1']
  have eq : (1 - (3 - E) * t) ^ 2 * ((-15*(E - 2)^2*t^5/4 + 5*(E - 2)^2*t^4/4 + (E - 2)^2*t^3 + 3*(E - 2)^2*t^2/4 + (E - 2)^2*t/2 + (E - 2)^2/4 + t^4/2 + t^3/2 + t^2/2 + t/2 + 1/2) - X * (-331*(E - 2)^2*t^5/12 + 113*(E - 2)^2*t^4/12 + 23*(E - 2)^2*t^3/3 + 23*(E - 2)^2*t^2/4 + 7*(E - 2)^2*t/2 + 5*(E - 2)^2/4 + 7*t^4/2 + 19*t^3/6 + 5*t^2/2 + 3*t/2 + 1/2)) * (4 * E ^ 2)
      - (E ^ 2 - 4 * E ^ 3 + E ^ 4 + 20 * E - 22) = t * (-15*E^6*t^6 + 5*E^6*t^5 + 4*E^6*t^4 + 3*E^6*t^3 + 2*E^6*t^2 + E^6*t + 150*E^5*t^6 - 80*E^5*t^5 - 30*E^5*t^4 - 22*E^5*t^3 - 14*E^5*t^2 - 6*E^5*t + 2*E^5 - 1334*E^4*t^6/3 + 1078*E^4*t^5/3 + 103*E^4*t^4/3 + 39*E^4*t^3 + 24*E^4*t^2 + 9*E^4*t - 12*E^4 - 610*E^3*t^6/3 - 584*E^3*t^5/3 + 610*E^3*t^4/3 + 266*E^3*t^3/3 + 46*E^3*t^2 + 6*E^3*t + 18*E^3 + 10627*E^2*t^6/3 - 7183*E^2*t^5/3 - 1619*E^2*t^4/3 - 1288*E^2*t^3/3 - 626*E^2*t^2/3 - 6*E^2*t + 30*E^2 - 6620*E*t^6 + 17624*E*t^5/3 + 724*E*t^4/3 + 584*E*t^3 + 728*E*t^2/3 - 56*E*t - 108*E + 3972*t^6 - 4130*t^5 + 634*t^4/3 - 812*t^3/3 - 244*t^2/3 + 72*t + 70) := by
    linear_combination (-4 * (1 - (3 - E) * t) ^ 2 * (-331*(E - 2)^2*t^5/12 + 113*(E - 2)^2*t^4/12 + 23*(E - 2)^2*t^3/3 + 23*(E - 2)^2*t^2/4 + 7*(E - 2)^2*t/2 + 5*(E - 2)^2/4 + 7*t^4/2 + 19*t^3/6 + 5*t^2/2 + 3*t/2 + 1/2)) * hX
  have := mul_nonneg ht0 hD
  rw [← sub_nonneg, eq]
  exact this

lemma part3 (E : ℝ) (h1 : 2718281828 / 1000000000 < E) :
    (474035 / 1000000 : ℝ) * (4 * E ^ 2) ≤ E ^ 2 - 4 * E ^ 3 + E ^ 4 + 20 * E - 22 := by
  obtain ⟨d, rfl⟩ : ∃ d, E = 2718281828 / 1000000000 + d := ⟨E - 2718281828 / 1000000000, by ring⟩
  have hd0 : 0 ≤ d := by linarith
  nlinarith [pow_nonneg hd0 2, pow_nonneg hd0 3, pow_nonneg hd0 4]

end Aux_RandomOrderCRS_minimum_after_7

open RandomOrderCRS Aux_RandomOrderCRS_minimum_after_7 in
theorem solution :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      cStar ≤ a₁ t * ∫ y in (0 : ℝ)..1, exp (-2 * y * (1 - t)) * (1 + a₁ 1 * (1 - t) * y ^ 2)) ∧
    (a₁ 0 * ∫ y in (0 : ℝ)..1, exp (-2 * y * (1 - 0)) * (1 + a₁ 1 * (1 - 0) * y ^ 2)) = cStar ∧
    (0.474035 : ℝ) ≤ cStar := by
  have e1 := Real.exp_one_gt_d9
  have e2 := Real.exp_one_lt_d9
  have hX : exp (-2) * exp 1 ^ 2 = 1 := by
    rw [sq, ← exp_add, ← exp_add]; norm_num
  have hA1 : a₁ 1 = (exp 1 - 2) ^ 2 := by unfold RandomOrderCRS.a₁; ring
  have hA0 : 0 ≤ a₁ 1 := by rw [hA1]; positivity
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have hint : ∫ y in (0:ℝ)..1, exp (-2 * y) * pexpr t (a₁ 1) y ≤
        ∫ y in (0:ℝ)..1, exp (-2 * y * (1 - t)) * (1 + a₁ 1 * (1 - t) * y ^ 2) := by
      apply intervalIntegral.integral_mono_on zero_le_one
      · apply Continuous.intervalIntegrable
        unfold pexpr
        fun_prop
      · apply Continuous.intervalIntegrable
        fun_prop
      intro y hy
      have hx : 0 ≤ 2 * y * t := mul_nonneg (mul_nonneg (by norm_num) hy.1) ht.1
      have hT : 1 + 2 * y * t + (2 * y * t) ^ 2 / 2 + (2 * y * t) ^ 3 / 6 + (2 * y * t) ^ 4 / 24
          ≤ exp (2 * y * t) := by
        have h := Real.sum_le_exp_of_nonneg hx 5
        have hs : ∑ i ∈ Finset.range 5, (2 * y * t) ^ i / (i.factorial : ℝ) =
            1 + 2 * y * t + (2 * y * t) ^ 2 / 2 + (2 * y * t) ^ 3 / 6 + (2 * y * t) ^ 4 / 24 := by
          norm_num [Finset.sum_range_succ, Nat.factorial] <;> ring
        rw [hs] at h
        exact h
      have hB : 0 ≤ 1 + a₁ 1 * (1 - t) * y ^ 2 := by
        have : 0 ≤ 1 - t := by linarith [ht.2]
        have : 0 ≤ a₁ 1 * (1 - t) * y ^ 2 := mul_nonneg (mul_nonneg hA0 this) (sq_nonneg y)
        linarith
      have hsplit : exp (-2 * y * (1 - t)) = exp (-2 * y) * exp (2 * y * t) := by
        rw [← exp_add]; congr 1; ring
      rw [hsplit, mul_assoc]
      unfold pexpr
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT hB) (exp_pos _).le
    have hval : ∫ y in (0:ℝ)..1, exp (-2 * y) * pexpr t (a₁ 1) y =
        hor (lt t (a₁ 1)) 0 - exp (-2) * hor (lt t (a₁ 1)) 1 :=
      integral_hor _ _ (fun y => by simp only [lt, hor, horD, pexpr]; ring)
    have ha0 : 0 ≤ a₁ t := by unfold RandomOrderCRS.a₁; positivity
    have halg := alg (exp 1) (exp (-2)) t hX (by linarith) (by linarith) ht.1 ht.2
    rw [← hA1] at halg
    calc cStar ≤ a₁ t * (hor (lt t (a₁ 1)) 0 - exp (-2) * hor (lt t (a₁ 1)) 1) := halg
      _ = a₁ t * ∫ y in (0:ℝ)..1, exp (-2 * y) * pexpr t (a₁ 1) y := by rw [hval]
      _ ≤ _ := mul_le_mul_of_nonneg_left hint ha0
  · have ha0 : a₁ 0 = 1 := by unfold RandomOrderCRS.a₁; ring
    have hval := integral_hor [1 / 2 + a₁ 1 / 4, a₁ 1 / 2, a₁ 1 / 2]
      (fun y => exp (-2 * y * (1 - 0)) * (1 + a₁ 1 * (1 - 0) * y ^ 2))
      (fun y => by simp only [sub_zero, mul_one, hor, horD]; ring)
    rw [hval, ha0, one_mul]
    simp only [hor]
    unfold RandomOrderCRS.cStar
    rw [hA1, eq_div_iff (by positivity)]
    linear_combination (-(2 + 5 * (exp 1 - 2) ^ 2)) * hX
  · unfold RandomOrderCRS.cStar
    rw [le_div_iff₀ (by positivity)]
    have h := part3 (exp 1) (by linarith)
    have h' : (0.474035:ℝ) = 474035 / 1000000 := by norm_num
    rw [h']
    exact h
