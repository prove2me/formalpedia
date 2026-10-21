-- Prove2me | solution 1 for QApproxCount.Counting.eqs_7_12
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:48:28.368461+00:00
-- url     : https://prove2.me/submissions/b2398adc-dd2e-497a-a676-64d8abf83b23

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm
set_option autoImplicit false

open QApproxCount.Counting MeasureTheory
open scoped Classical

lemma coin_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (A : Set ℕ) :
    (coin p m).toOuterMeasure A ≤
      ∑ k ∈ Finset.range (m + 1),
        if k ∈ A then ENNReal.ofReal ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) else 0 := by
  have hproj : ((Set.projIcc (0 : ℝ) 1 zero_le_one p : unitInterval) : ℝ) = p := by
    simp [Set.projIcc, max_eq_right hp0, min_eq_right hp1]
  refine (PMF.toOuterMeasure_apply_le_toMeasure_apply _ A).trans ?_
  unfold coin
  rw [Measure.toPMF_toMeasure, ProbabilityTheory.binomial_eq_sum_dirac, hproj]
  have hI : Finset.Iic m = Finset.range (m + 1) := by ext; simp [Nat.lt_succ_iff]
  rw [hI, Measure.finset_sum_apply]
  refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
  rw [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
  by_cases hk : k ∈ A <;> simp [hk, Set.indicator]

lemma tail_sum_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (a l : ℝ) (hl : 0 ≤ l) :
    ∑ k ∈ Finset.range (m + 1),
        (if a ≤ (k : ℝ) then (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0) ≤
      Real.exp (-(l * a)) * (1 - p + p * Real.exp l) ^ m := by
  have hbin : (1 - p + p * Real.exp l) ^ m =
      ∑ k ∈ Finset.range (m + 1), (p * Real.exp l) ^ k * (1 - p) ^ (m - k) * (m.choose k : ℝ) :=
    add_pow (p * Real.exp l) (1 - p) m ▸ by rw [add_comm]
  rw [hbin, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1p : 0 ≤ 1 - p := by linarith
  by_cases hk : a ≤ (k : ℝ)
  · rw [if_pos hk]
    have : Real.exp (-(l * a)) * ((p * Real.exp l) ^ k * (1 - p) ^ (m - k) * (m.choose k : ℝ))
        = Real.exp (l * (k - a)) * ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have : Real.exp (l * (k - a)) = Real.exp (-(l * a)) * Real.exp (↑k * l) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]; ring
    rw [this]
    have hge : 1 ≤ Real.exp (l * (k - a)) := Real.one_le_exp (by nlinarith)
    have hnn : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by positivity
    nlinarith
  · rw [if_neg hk]; positivity


lemma oddFloor_bounds (k : ℕ) :
    (oddFloor k : ℝ) ≤ (1.05 : ℝ) ^ k ∧ (1.05 : ℝ) ^ k - 2 < (oddFloor k : ℝ) := by
  have hx : (1 : ℝ) ≤ (1.05 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hf1 : 1 ≤ ⌊(1.05 : ℝ) ^ k⌋₊ := Nat.le_floor (by simpa using hx)
  have hfl := Nat.floor_le (by linarith : (0 : ℝ) ≤ (1.05 : ℝ) ^ k)
  have hfu := Nat.lt_floor_add_one ((1.05 : ℝ) ^ k)
  unfold oddFloor
  split_ifs with h
  · constructor <;> linarith
  · rw [Nat.cast_sub hf1]
    push_cast
    constructor <;> linarith

lemma coin_lower (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    (coin p m).toOuterMeasure {h : ℕ | (h : ℝ) < 0.95 * (m : ℝ)} ≤
      ENNReal.ofReal (((1.01 : ℝ) ^ 19 * (1 - p + p * ((1.01 : ℝ) ^ 20)⁻¹)) ^ m) := by
  refine (coin_le p hp0 hp1 m _).trans ?_
  set y : ℝ := 1.01 with hy
  have hy1 : (1 : ℝ) ≤ y := by rw [hy]; norm_num
  set q : ℝ := (y ^ 20)⁻¹ with hq
  have h1p : 0 ≤ 1 - p := by linarith
  have hnn : ∀ k ∈ Finset.range (m + 1),
      0 ≤ (if k ∈ {h : ℕ | (h : ℝ) < 0.95 * (m : ℝ)} then
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0) := by
    intro k _
    split_ifs
    · positivity
    · exact le_rfl
  have hconv : ∑ k ∈ Finset.range (m + 1),
        (if k ∈ {h : ℕ | (h : ℝ) < 0.95 * (m : ℝ)} then
          ENNReal.ofReal ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) else 0) =
      ENNReal.ofReal (∑ k ∈ Finset.range (m + 1),
        (if k ∈ {h : ℕ | (h : ℝ) < 0.95 * (m : ℝ)} then
          (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0)) := by
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ {h : ℕ | (h : ℝ) < 0.95 * (m : ℝ)} <;> simp [hk]
  rw [hconv]
  apply ENNReal.ofReal_le_ofReal
  have hbin : (y ^ 19 * (1 - p + p * q)) ^ m =
      ∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * (y ^ (19 * m) * q ^ k) := by
    rw [mul_pow, ← pow_mul]
    rw [add_comm (1 - p) (p * q), add_pow (p * q) (1 - p) m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]; ring
  rw [hbin]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k ∈ {h : ℕ | (h : ℝ) < 0.95 * (m : ℝ)}
  · rw [if_pos hk]
    have hk' : 20 * k ≤ 19 * m := by
      have : (k : ℝ) < 0.95 * (m : ℝ) := hk
      have : (20 * k : ℝ) < 19 * m := by linarith
      exact_mod_cast this.le
    have : 1 ≤ y ^ (19 * m) * q ^ k := by
      have h2 : (y ^ 20) ^ k ≤ y ^ (19 * m) := by
        rw [← pow_mul]; exact pow_le_pow_right₀ hy1 (by omega)
      have h3 : 0 < (y ^ 20) ^ k := by positivity
      have e : y ^ (19 * m) * q ^ k = y ^ (19 * m) / (y ^ 20) ^ k := by
        rw [hq, inv_pow, div_eq_mul_inv]
      rw [e, one_le_div h3]; exact h2
    have hnn' : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by positivity
    nlinarith
  · rw [if_neg hk]
    have : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * (y ^ (19 * m) * q ^ k) := by positivity
    exact this

theorem solution (θ δ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 0.001) (k₀ : ℕ)
    (hk₀ : θ * (1.05 : ℝ) ^ k₀ ≤ 0.9) (hk₀max : 0.9 < θ * (1.05 : ℝ) ^ (k₀ + 1))
    (hδ : 0 < δ) (m : ℕ) (hm : 5000 * Real.log (5 / δ) ≤ (m : ℝ)) :
    0.96 ≤ Real.sin ((oddFloor (k₀ + 10) : ℝ) * θ) ^ 2 ∧
      (coin (Real.sin ((oddFloor (k₀ + 10) : ℝ) * θ) ^ 2) m).toOuterMeasure
          {h : ℕ | (h : ℝ) < 0.95 * (m : ℝ)} ≤ ENNReal.ofReal (δ / 5) := by
  obtain ⟨hr1, hr2⟩ := oddFloor_bounds (k₀ + 10)
  set r : ℝ := (oddFloor (k₀ + 10) : ℝ) with hr
  have hX1 : θ * (1.05 : ℝ) ^ (k₀ + 10) = θ * (1.05 : ℝ) ^ (k₀ + 1) * (1.05 : ℝ) ^ 9 := by
    rw [show k₀ + 10 = (k₀ + 1) + 9 by ring, pow_add]; ring
  have hX2 : θ * (1.05 : ℝ) ^ (k₀ + 10) = θ * (1.05 : ℝ) ^ k₀ * (1.05 : ℝ) ^ 10 := by
    rw [pow_add]; ring
  have h9 : (1.05 : ℝ) ^ 9 > 1.55 := by norm_num
  have hu_lo : 1.39 ≤ r * θ := by
    have : (1.05 : ℝ) ^ (k₀ + 10) * θ - 2 * θ < r * θ := by nlinarith
    have h9' : (1.05 : ℝ) ^ 9 * 0.9 > 1.396 := by norm_num
    nlinarith
  have hu_hi : r * θ ≤ 1.47 := by
    have : r * θ ≤ (1.05 : ℝ) ^ (k₀ + 10) * θ := by nlinarith
    have h10 : (1.05 : ℝ) ^ 10 * 0.9 < 1.47 := by norm_num
    nlinarith
  have hsin : 0.96 ≤ Real.sin (r * θ) ^ 2 := by
    have hpi := Real.pi_gt_d4
    have hc : Real.sin (r * θ) = Real.cos (Real.pi / 2 - r * θ) := (Real.cos_pi_div_two_sub _).symm
    have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 2 - r * θ)
    have hy0 : 0 ≤ Real.pi / 2 - r * θ := by linarith
    have hy1 : Real.pi / 2 - r * θ ≤ 0.2 := by linarith [Real.pi_lt_d4]
    have : 0.98 ≤ Real.sin (r * θ) := by
      rw [hc]; nlinarith
    nlinarith
  refine ⟨hsin, ?_⟩
  have hp1 : Real.sin (r * θ) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  refine (coin_lower _ (by positivity) hp1 m).trans ?_
  apply ENNReal.ofReal_le_ofReal
  set p : ℝ := Real.sin (r * θ) ^ 2 with hp
  have hc : (1.01 : ℝ) ^ 19 * (1 - p + p * ((1.01 : ℝ) ^ 20)⁻¹) ≤ 0.9989 := by
    have h1 : (1.01 : ℝ) ^ 19 * (1 - 0.96 + 0.96 * ((1.01 : ℝ) ^ 20)⁻¹) ≤ 0.9989 := by norm_num
    have h2 : (1.01 : ℝ) ^ 19 * (1 - p + p * ((1.01 : ℝ) ^ 20)⁻¹) ≤
        (1.01 : ℝ) ^ 19 * (1 - 0.96 + 0.96 * ((1.01 : ℝ) ^ 20)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have : ((1.01 : ℝ) ^ 20)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      nlinarith
    linarith
  have hc0 : 0 ≤ (1.01 : ℝ) ^ 19 * (1 - p + p * ((1.01 : ℝ) ^ 20)⁻¹) := by
    have : ((1.01 : ℝ) ^ 20)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have : 0 ≤ ((1.01 : ℝ) ^ 20)⁻¹ := by positivity
    have : 0 ≤ p := by positivity
    positivity
  have he : (0.9989 : ℝ) ≤ Real.exp (-(1 / 5000)) := by
    have := Real.add_one_le_exp (-(1 / 5000 : ℝ))
    linarith
  calc ((1.01 : ℝ) ^ 19 * (1 - p + p * ((1.01 : ℝ) ^ 20)⁻¹)) ^ m ≤ (Real.exp (-(1 / 5000))) ^ m :=
        pow_le_pow_left₀ hc0 (hc.trans he) m
    _ = Real.exp (-((m : ℝ) / 5000)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-Real.log (5 / δ)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = δ / 5 := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
