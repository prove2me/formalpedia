-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P08.smallStrengthExpansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:14:30.772988+00:00
-- url     : https://prove2.me/submissions/f65335f2-5fb1-4691-af9f-38fa38ecf3d7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable



lemma g53f_binEnt (x : ℝ) (h1 : -1 < x) (h2 : x < 1) :
    Real.binEntropy ((1 + x) / 2) =
      Real.log 2 - ((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) / 2 := by
  have ha : (0:ℝ) < 1 + x := by linarith
  have hb : (0:ℝ) < 1 - x := by linarith
  rw [Real.binEntropy]
  have e1 : ((1 + x) / 2)⁻¹ = 2 / (1 + x) := by rw [inv_div]
  have e2 : (1 - (1 + x) / 2)⁻¹ = 2 / (1 - x) := by
    rw [show 1 - (1 + x) / 2 = (1 - x) / 2 by ring, inv_div]
  rw [e1, e2, Real.log_div (by norm_num) ha.ne', Real.log_div (by norm_num) hb.ne']
  ring

lemma g53f_tlog (t : ℝ) (ht : 0 < t) :
    0 ≤ t * Real.log t - (t - 1) ∧ t * Real.log t - (t - 1) ≤ (t - 1) ^ 2 := by
  have h1 := Real.log_le_sub_one_of_pos ht
  have h2 := Real.one_sub_inv_le_log_of_pos ht
  constructor
  · have : t * (1 - t⁻¹) ≤ t * Real.log t := mul_le_mul_of_nonneg_left h2 ht.le
    have e : t * (1 - t⁻¹) = t - 1 := by field_simp
    linarith
  · have : t * Real.log t ≤ t * (t - 1) := mul_le_mul_of_nonneg_left h1 ht.le
    nlinarith

lemma g53f_bregman (a y : ℝ) (ha1 : -1 < a) (ha2 : a < 1) (hy1 : -1 < y) (hy2 : y < 1) :
    0 ≤ ((1 + y) * Real.log (1 + y) + (1 - y) * Real.log (1 - y)) -
        ((1 + a) * Real.log (1 + a) + (1 - a) * Real.log (1 - a)) -
        Real.log ((1 + a) / (1 - a)) * (y - a) ∧
    ((1 + y) * Real.log (1 + y) + (1 - y) * Real.log (1 - y)) -
        ((1 + a) * Real.log (1 + a) + (1 - a) * Real.log (1 - a)) -
        Real.log ((1 + a) / (1 - a)) * (y - a) ≤
      (y - a) ^ 2 * (1 / (1 + a) + 1 / (1 - a)) := by
  have hA : (0:ℝ) < 1 + a := by linarith
  have hB : (0:ℝ) < 1 - a := by linarith
  have hY : (0:ℝ) < 1 + y := by linarith
  have hZ : (0:ℝ) < 1 - y := by linarith
  set t := (1 + y) / (1 + a) with ht
  set u := (1 - y) / (1 - a) with hu
  have tp : 0 < t := div_pos hY hA
  have up : 0 < u := div_pos hZ hB
  clear_value t u
  have et : 1 + y = (1 + a) * t := by rw [ht]; field_simp
  have eu : 1 - y = (1 - a) * u := by rw [hu]; field_simp
  have lt : Real.log (1 + y) = Real.log (1 + a) + Real.log t := by
    rw [et, Real.log_mul hA.ne' tp.ne']
  have lu : Real.log (1 - y) = Real.log (1 - a) + Real.log u := by
    rw [eu, Real.log_mul hB.ne' up.ne']
  have lk : Real.log ((1 + a) / (1 - a)) = Real.log (1 + a) - Real.log (1 - a) :=
    Real.log_div hA.ne' hB.ne'
  have key : ((1 + y) * Real.log (1 + y) + (1 - y) * Real.log (1 - y)) -
        ((1 + a) * Real.log (1 + a) + (1 - a) * Real.log (1 - a)) -
        Real.log ((1 + a) / (1 - a)) * (y - a) =
      (1 + a) * (t * Real.log t - (t - 1)) + (1 - a) * (u * Real.log u - (u - 1)) := by
    rw [lt, lu, lk]
    linear_combination (Real.log t - 1) * et + (Real.log u - 1) * eu
  rw [key]
  obtain ⟨t1, t2⟩ := g53f_tlog t tp
  obtain ⟨u1, u2⟩ := g53f_tlog u up
  constructor
  · positivity
  · have e1 : (1 + a) * (t - 1) ^ 2 = (y - a) ^ 2 * (1 / (1 + a)) := by
      rw [ht]; field_simp; ring
    have e2 : (1 - a) * (u - 1) ^ 2 = (y - a) ^ 2 * (1 / (1 - a)) := by
      rw [hu]; field_simp; ring
    have := mul_le_mul_of_nonneg_left t2 hA.le
    have := mul_le_mul_of_nonneg_left u2 hB.le
    nlinarith

lemma g53f_psi4 (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) - x ^ 2| ≤ 7 * x ^ 4 := by
  have hx1 : |x| < 1 := by linarith
  have hx2 : |-x| < 1 := by rw [abs_neg]; exact hx1
  have h1 := Real.abs_log_sub_add_sum_range_le hx1 3
  have h2 := Real.abs_log_sub_add_sum_range_le hx2 3
  rw [abs_neg] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add] at h1 h2
  have hpos : (1:ℝ) / 2 ≤ 1 - |x| := by linarith
  have hx4 : |x| ^ (3 + 1) = x ^ 4 := by
    rw [show 3 + 1 = 4 by rfl, pow_abs, abs_of_nonneg (by positivity)]
  rw [hx4] at h1 h2
  have b : x ^ 4 / (1 - |x|) ≤ 2 * x ^ 4 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_two_nonneg (x^2)]
  have E1 : |x + x ^ 2 / 2 + x ^ 3 / 3 + Real.log (1 - x)| ≤ 2 * x ^ 4 := by
    refine le_trans (le_of_eq ?_) (h1.trans b); congr 1; push_cast; ring
  have E2 : |-x + x ^ 2 / 2 - x ^ 3 / 3 + Real.log (1 + x)| ≤ 2 * x ^ 4 := by
    refine le_trans (le_of_eq ?_) (h2.trans b); congr 1; push_cast; ring
  set e1 := x + x ^ 2 / 2 + x ^ 3 / 3 + Real.log (1 - x) with he1
  set e2 := -x + x ^ 2 / 2 - x ^ 3 / 3 + Real.log (1 + x) with he2
  have key : ((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) - x ^ 2 =
      (1 + x) * e2 + (1 - x) * e1 + 2 / 3 * x ^ 4 := by
    rw [he1, he2]; ring
  rw [key]
  have hxa := abs_le.mp hx
  have q1 : |(1 + x) * e2| ≤ 3 / 2 * (2 * x ^ 4) := by
    rw [abs_mul]
    exact mul_le_mul (by rw [abs_of_pos (by linarith)]; linarith) E2 (abs_nonneg _) (by norm_num)
  have q2 : |(1 - x) * e1| ≤ 3 / 2 * (2 * x ^ 4) := by
    rw [abs_mul]
    exact mul_le_mul (by rw [abs_of_pos (by linarith)]; linarith) E1 (abs_nonneg _) (by norm_num)
  have x4 : 0 ≤ x ^ 4 := by positivity
  calc _ ≤ |(1 + x) * e2| + |(1 - x) * e1| + |2 / 3 * x ^ 4| := abs_add_three _ _ _
    _ ≤ _ := by
      have : |2 / 3 * x ^ 4| = 2 / 3 * x ^ 4 := abs_of_nonneg (by positivity)
      linarith

lemma g53f_atanh (a : ℝ) (h0 : 0 < a) (h1 : a < 1) :
    2 * a < Real.log ((1 + a) / (1 - a)) := by
  have ha : |a| < 1 := by rw [abs_of_pos h0]; exact h1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one ha
  rw [← Real.log_div (by linarith) (by linarith)] at hs
  have := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) hs
  simp [Finset.sum_range_succ] at this
  nlinarith [pow_pos h0 3]

lemma g53f_T2T3 (a b s K P3 P4 r : ℝ) (ha : 0 < a) (hb : 0 < b) (har : a ≤ r)
    (hr2 : r ^ 2 = a ^ 2 + b * s ^ 2)
    (hT2 : 0 ≤ P3 - P4 - K * (r - a) ∧ P3 - P4 - K * (r - a) ≤ (r - a) ^ 2 * (2 / b)) :
    |P3 - P4 - K * (r - a)| + |K * (r - a - b * s ^ 2 / (2 * a))| ≤
      (b / (2 * a ^ 2) + |K| * b ^ 2 / (8 * a ^ 3)) * s ^ 4 := by
  set w := r - a with hw
  have w0 : 0 ≤ w := by rw [hw]; linarith
  have hwr : w * (r + a) = b * s ^ 2 := by rw [hw]; nlinarith
  have hw1 : w * (2 * a) ≤ b * s ^ 2 := by
    rw [← hwr]; exact mul_le_mul_of_nonneg_left (by linarith) w0
  have hw2 : w ≤ b * s ^ 2 / (2 * a) := by rw [le_div_iff₀ (by positivity)]; exact hw1
  have hw3 : w ^ 2 ≤ (b * s ^ 2 / (2 * a)) ^ 2 := pow_le_pow_left₀ w0 hw2 2
  have e3 : r - a - b * s ^ 2 / (2 * a) = -(w ^ 2 / (2 * a)) := by
    rw [← hwr]; field_simp; rw [hw]; ring
  rw [e3, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ w ^ 2 / (2 * a)),
    abs_of_nonneg hT2.1]
  have q2 : w ^ 2 * (2 / b) ≤ (b * s ^ 2 / (2 * a)) ^ 2 * (2 / b) :=
    mul_le_mul_of_nonneg_right hw3 (by positivity)
  have q3 : |K| * (w ^ 2 / (2 * a)) ≤ |K| * ((b * s ^ 2 / (2 * a)) ^ 2 / (2 * a)) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hw3 (by positivity)) (abs_nonneg _)
  have e4 : (b * s ^ 2 / (2 * a)) ^ 2 * (2 / b) = b / (2 * a ^ 2) * s ^ 4 := by
    field_simp
  have e5 : |K| * ((b * s ^ 2 / (2 * a)) ^ 2 / (2 * a)) = |K| * b ^ 2 / (8 * a ^ 3) * s ^ 4 := by
    field_simp; ring
  have := hT2.2
  rw [add_mul]
  linarith

theorem solution (p : ℝ) (hp : 0 < p) (hpUpper : p < 1) :
    0 < gainCoefficient p ∧
    ∃ C > (0 : ℝ), ∃ delta > (0 : ℝ), delta ≤ 1 ∧ ∀ s : ℝ, |s| ≤ delta →
      |twoRoundRate p s - (1 - binEntropy2 (p / 2) + gainCoefficient p * s ^ 2)| ≤ C * |s| ^ 4 := by
  have ha0 : 0 < 1 - p := by linarith
  have ha1 : 1 - p < 1 := by linarith
  have hb : 0 < 1 - (1 - p) ^ 2 := by nlinarith
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK := g53f_atanh (1 - p) ha0 ha1
  constructor
  · unfold gainCoefficient inverseTanh
    apply mul_pos (by positivity)
    rw [sub_pos, lt_div_iff₀ ha0]; linarith
  set a := 1 - p with hadef
  set b := 1 - a ^ 2 with hbdef
  set K := Real.log ((1 + a) / (1 - a)) with hKdef
  set L := Real.log 2 with hLdef
  refine ⟨(14 + (b / (2 * a ^ 2) + |K| * b ^ 2 / (8 * a ^ 3))) / (2 * L), by positivity,
    1 / 2, by norm_num, by norm_num, fun s hs => ?_⟩
  have hsa := abs_le.mp hs
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith
  set r := Real.sqrt (a ^ 2 + b * s ^ 2) with hrdef
  have hr2 : r ^ 2 = a ^ 2 + b * s ^ 2 := Real.sq_sqrt (by positivity)
  have har : a ≤ r := Real.le_sqrt_of_sq_le (by nlinarith)
  have hr1 : r < 1 := by
    rw [hrdef, Real.sqrt_lt' (by norm_num)]
    nlinarith
  have has : |a * s| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos ha0]; nlinarith [abs_nonneg s]
  have hasa := abs_le.mp has
  unfold twoRoundRate binEntropy2
  have hp2 : Real.binEntropy (p / 2) = Real.binEntropy ((1 + a) / 2) := by
    rw [← Real.binEntropy_one_sub]; congr 1; rw [hadef]; ring
  rw [hp2, g53f_binEnt _ (by linarith) (by linarith), g53f_binEnt _ (by linarith) (by linarith),
    g53f_binEnt _ (by linarith) (by linarith), g53f_binEnt _ (by linarith) (by linarith)]
  have h1 := g53f_psi4 (a * s) has
  have h2 := g53f_psi4 s hs
  have h3 := g53f_bregman a r (by linarith) ha1 (by linarith) hr1
  have e2b : 1 / (1 + a) + 1 / (1 - a) = 2 / b := by
    have n1 : (1 + a) ≠ 0 := by linarith
    have n2 : (1 - a) ≠ 0 := by linarith
    rw [div_add_div _ _ n1 n2, div_eq_div_iff (mul_ne_zero n1 n2) hb.ne', hbdef]; ring
  rw [e2b] at h3
  have hT := g53f_T2T3 a b s K _ _ r ha0 hb har hr2 h3
  set P1 := (1 + a * s) * Real.log (1 + a * s) + (1 - a * s) * Real.log (1 - a * s)
  set P2 := (1 + s) * Real.log (1 + s) + (1 - s) * Real.log (1 - s)
  set P3 := (1 + r) * Real.log (1 + r) + (1 - r) * Real.log (1 - r)
  set P4 := (1 + a) * Real.log (1 + a) + (1 - a) * Real.log (1 - a)
  have hG : gainCoefficient p = b / (2 * L) * (K / 2 / a - 1) := by
    unfold gainCoefficient inverseTanh; rfl
  rw [hG]
  have eD : 1 - (L - P1 / 2) / L + (L - P2 / 2) / L - (L - P3 / 2) / L -
      (1 - (L - P4 / 2) / L + b / (2 * L) * (K / 2 / a - 1) * s ^ 2) =
      (((P1 - (a * s) ^ 2) - (P2 - s ^ 2)) + (P3 - P4 - K * (r - a)) +
        K * (r - a - b * s ^ 2 / (2 * a))) / (2 * L) := by
    field_simp; rw [hbdef]; ring
  rw [eD, abs_div, abs_of_pos (by positivity : 0 < 2 * L), div_le_iff₀ (by positivity)]
  have hs4 : |s| ^ 4 = s ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
  rw [hs4]
  have ha4 : (a * s) ^ 4 ≤ s ^ 4 := by
    rw [mul_pow]
    have : a ^ 4 ≤ 1 := pow_le_one₀ ha0.le ha1.le
    nlinarith [pow_two_nonneg (s ^ 2)]
  have hT1 : |(P1 - (a * s) ^ 2) - (P2 - s ^ 2)| ≤ 14 * s ^ 4 := by
    calc _ ≤ |P1 - (a * s) ^ 2| + |P2 - s ^ 2| := abs_sub _ _
      _ ≤ _ := by linarith
  have tri := abs_add_three ((P1 - (a * s) ^ 2) - (P2 - s ^ 2)) (P3 - P4 - K * (r - a))
    (K * (r - a - b * s ^ 2 / (2 * a)))
  have e5 : (14 + (b / (2 * a ^ 2) + |K| * b ^ 2 / (8 * a ^ 3))) / (2 * L) * s ^ 4 * (2 * L) =
      14 * s ^ 4 + (b / (2 * a ^ 2) + |K| * b ^ 2 / (8 * a ^ 3)) * s ^ 4 := by
    field_simp
  rw [e5]
  linarith
