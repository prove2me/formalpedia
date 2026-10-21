-- Prove2me | solution 1 for QApproxCount.Counting.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:03:15.739896+00:00
-- url     : https://prove2.me/submissions/e7fefc11-db09-4b28-b399-10a949981c12

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm
set_option autoImplicit false

open QApproxCount.Counting MeasureTheory
open scoped Classical

lemma rot_core (θmin θmax γ : ℝ) (hθmin : 0 < θmin) (hγ : 0 < γ)
    (hmax : θmax = (1 + γ) * θmin) :
    |(rotK θmin θmax : ℝ) - 1 / (2 * γ)| ≤ 1 / 2 ∧
      |(rotR θmin θmax : ℝ) * θmin - Real.pi * (rotK θmin θmax : ℝ)| ≤ θmin := by
  have hK : θmin / (2 * (θmax - θmin)) = 1 / (2 * γ) := by
    have h1 := hγ.ne'
    have h2 := hθmin.ne'
    rw [hmax, show (1 + γ) * θmin - θmin = γ * θmin by ring]; field_simp
  constructor
  · have h := abs_sub_round (θmin / (2 * (θmax - θmin)))
    rw [hK] at h
    have e : (rotK θmin θmax : ℝ) = (round (1 / (2 * γ)) : ℝ) := by
      unfold rotK; rw [hK]
    rw [e, abs_sub_comm]; exact h
  · have hy := abs_sub_round ((Real.pi * (rotK θmin θmax : ℝ) / θmin - 1) / 2)
    have e : (rotR θmin θmax : ℝ) * θmin - Real.pi * (rotK θmin θmax : ℝ) =
        2 * θmin * ((round ((Real.pi * (rotK θmin θmax : ℝ) / θmin - 1) / 2) : ℝ) -
          (Real.pi * (rotK θmin θmax : ℝ) / θmin - 1) / 2) := by
      unfold rotR
      push_cast
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * θmin), abs_sub_comm]
    nlinarith

lemma sin_sq_shift (x : ℝ) (k : ℤ) : Real.sin (x + k * Real.pi) ^ 2 = Real.sin x ^ 2 := by
  rw [Real.sin_add_int_mul_pi, mul_pow]
  rcases Int.even_or_odd k with h | h <;> simp [h.neg_one_zpow]

/-- facts about k and r. -/
lemma rot_facts (θmin θmax γ : ℝ) (hθmin : 0 < θmin) (hγ : 0 < γ) (hγ1 : γ ≤ 0.7)
    (hmax : θmax = (1 + γ) * θmin) (hθmax : θmax ≤ 0.002) :
    0.5 - γ / 2 ≤ γ * (rotK θmin θmax : ℝ) ∧ γ * (rotK θmin θmax : ℝ) ≤ 0.5 + γ / 2 ∧
    (1 + γ) * θmin ≤ 0.002 ∧
    |(rotR θmin θmax : ℝ) * θmin - Real.pi * (rotK θmin θmax : ℝ)| ≤ θmin ∧
    0 < (rotR θmin θmax : ℝ) := by
  obtain ⟨h1, h2⟩ := rot_core θmin θmax γ hθmin hγ hmax
  have hk := abs_le.mp h1
  have hγk : γ * (1 / (2 * γ)) = 1 / 2 := by field_simp
  have hA : 0.5 - γ / 2 ≤ γ * (rotK θmin θmax : ℝ) := by
    have := mul_le_mul_of_nonneg_left hk.1 hγ.le
    nlinarith
  have hB : γ * (rotK θmin θmax : ℝ) ≤ 0.5 + γ / 2 := by
    have := mul_le_mul_of_nonneg_left hk.2 hγ.le
    nlinarith
  have hθ : (1 + γ) * θmin ≤ 0.002 := by rw [← hmax]; exact hθmax
  refine ⟨hA, hB, hθ, h2, ?_⟩
  have hkpos : (0 : ℝ) < (rotK θmin θmax : ℝ) := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have hk1 : (1 : ℝ) ≤ (rotK θmin θmax : ℝ) := by
    have : (0 : ℤ) < rotK θmin θmax := by exact_mod_cast hkpos
    exact_mod_cast this
  have hd := (abs_le.mp h2).1
  have hθ2 : θmin ≤ 0.002 := by nlinarith
  have hpi := Real.pi_gt_three
  have : 0 < (rotR θmin θmax : ℝ) * θmin := by nlinarith
  exact pos_of_mul_pos_left this hθmin.le

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

lemma sin_lb (x : ℝ) (h1 : 0.42 ≤ x) (h2 : x ≤ 2.68) : 0.4076 ≤ Real.sin x := by
  have hpi := Real.pi_gt_d4
  have hpi2 : Real.pi / 2 ≤ Real.pi - 0.42 := by linarith
  have h0 : 0.4076 ≤ Real.sin 0.42 := by
    have := Real.sin_gt_sub_cube (x := 0.42) (by norm_num)
    norm_num at this ⊢
    linarith
  rcases le_total x (Real.pi / 2) with h | h
  · refine h0.trans (Real.sin_le_sin_of_le_of_le_pi_div_two ?_ h h1)
    linarith [Real.pi_pos]
  · rw [← Real.sin_pi_sub]
    refine h0.trans (Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ ?_)
    · linarith [Real.pi_pos]
    · linarith
    · linarith


theorem low_zone (θmin θmax γ θ : ℝ) (hθmin : 0 < θmin) (hγ : 0 < γ) (hγ1 : γ ≤ 0.7)
    (hmax : θmax = (1 + γ) * θmin) (hθmax : θmax ≤ 0.002)
    (hlo : θmin ≤ θ) (hhi : θ ≤ θmax / (1 + 0.9 * γ)) :
    -0.002 ≤ (rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ) ∧
      (rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ) ≤ 0.27 ∧
      Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2 ≤ 0.075 := by
  obtain ⟨hA, hB, hθ, hd, hr⟩ := rot_facts θmin θmax γ hθmin hγ hγ1 hmax hθmax
  have hs : Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2 =
      Real.sin ((rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ)) ^ 2 := by
    rw [← sin_sq_shift ((rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ)) (rotK θmin θmax)]
    congr 2; ring
  rw [hs]
  have hθ2 : θmin ≤ 0.002 := by nlinarith
  set k : ℝ := (rotK θmin θmax : ℝ) with hk
  set r : ℝ := (rotR θmin θmax : ℝ) with hr'
  set d : ℝ := r * θmin - Real.pi * k with hd'
  have hdb := abs_le.mp hd
  have hu : 0 < 1 + 0.9 * γ := by linarith
  have hhi' : θ * (1 + 0.9 * γ) ≤ θmax := by rwa [le_div_iff₀ hu] at hhi
  have hlow : -0.002 ≤ r * θ - Real.pi * k := by
    have : r * θmin ≤ r * θ := mul_le_mul_of_nonneg_left hlo hr.le
    linarith [hdb.1]
  have hup : r * θ - Real.pi * k ≤ 0.27 := by
    have hpi := Real.pi_lt_d4
    have hpi0 := Real.pi_pos
    have h1 : r * (θ * (1 + 0.9 * γ)) ≤ r * θmax := mul_le_mul_of_nonneg_left hhi' hr.le
    have h2 : (1 + γ) * d ≤ (1 + γ) * θmin := mul_le_mul_of_nonneg_left hdb.2 (by linarith)
    have h3 : Real.pi * (γ * k) ≤ Real.pi * (0.5 + γ / 2) :=
      mul_le_mul_of_nonneg_left hB hpi0.le
    have h4 : Real.pi * γ ≤ 3.1416 * γ := mul_le_mul_of_nonneg_right hpi.le hγ.le
    have h5 : (r * θ - Real.pi * k) * (1 + 0.9 * γ) ≤ 0.27 * (1 + 0.9 * γ) := by
      have e : r * θmax = (1 + γ) * (d + Real.pi * k) := by rw [hmax, hd']; ring
      nlinarith
    exact le_of_mul_le_mul_right h5 hu
  refine ⟨hlow, hup, ?_⟩
  have h6 := Real.sin_sq_le_sq (x := r * θ - Real.pi * k)
  nlinarith

theorem high_zone (θmin θmax γ θ : ℝ) (hθmin : 0 < θmin) (hγ : 0 < γ) (hγ1 : γ ≤ 0.7)
    (hmax : θmax = (1 + γ) * θmin) (hθmax : θmax ≤ 0.002)
    (hlo : θmin * (1 + 0.9 * γ) ≤ θ) (hhi : θ ≤ θmax) :
    0.42 ≤ (rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ) ∧
      (rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ) ≤ 2.68 ∧
      0.165 ≤ Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2 := by
  obtain ⟨hA, hB, hθ, hd, hr⟩ := rot_facts θmin θmax γ hθmin hγ hγ1 hmax hθmax
  have hs : Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2 =
      Real.sin ((rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ)) ^ 2 := by
    rw [← sin_sq_shift ((rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ)) (rotK θmin θmax)]
    congr 2; ring
  rw [hs]
  have hθ2 : θmin ≤ 0.002 := by nlinarith
  set k : ℝ := (rotK θmin θmax : ℝ) with hk
  set r : ℝ := (rotR θmin θmax : ℝ) with hr'
  set d : ℝ := r * θmin - Real.pi * k with hd'
  have hdb := abs_le.mp hd
  have hpi := Real.pi_lt_d4
  have hpi' := Real.pi_gt_d4
  have hpi0 := Real.pi_pos
  have hlow : 0.42 ≤ r * θ - Real.pi * k := by
    have h1 : r * (θmin * (1 + 0.9 * γ)) ≤ r * θ := mul_le_mul_of_nonneg_left hlo hr.le
    have h2 : d * (1 + 0.9 * γ) ≥ -(θmin * (1 + 0.9 * γ)) := by
      have := mul_le_mul_of_nonneg_right hdb.1 (by linarith : (0:ℝ) ≤ 1 + 0.9 * γ)
      linarith
    have h3 : Real.pi * (0.5 - γ / 2) ≤ Real.pi * (γ * k) :=
      mul_le_mul_of_nonneg_left hA hpi0.le
    have h4 : Real.pi * 0.15 ≤ Real.pi * (0.5 - γ / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hpi0.le
    have e : r * (θmin * (1 + 0.9 * γ)) = (d + Real.pi * k) * (1 + 0.9 * γ) := by
      rw [hd']; ring
    nlinarith
  have hup : r * θ - Real.pi * k ≤ 2.68 := by
    have h1 : r * θ ≤ r * θmax := mul_le_mul_of_nonneg_left hhi hr.le
    have h2 : (1 + γ) * d ≤ (1 + γ) * θmin := mul_le_mul_of_nonneg_left hdb.2 (by linarith)
    have h3 : Real.pi * (γ * k) ≤ Real.pi * (0.5 + γ / 2) :=
      mul_le_mul_of_nonneg_left hB hpi0.le
    have h4 : Real.pi * γ ≤ 3.1416 * 0.7 := mul_le_mul hpi.le hγ1 hγ.le (by norm_num)
    have e : r * θmax = (1 + γ) * (d + Real.pi * k) := by rw [hmax, hd']; ring
    nlinarith
  refine ⟨hlow, hup, ?_⟩
  have := sin_lb _ hlow hup
  nlinarith


lemma coin_upper_gen (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (a b : ℕ) (A : Set ℕ) (hA : ∀ k ∈ A, a * m ≤ b * k) :
    (coin p m).toOuterMeasure A ≤
      ENNReal.ofReal (((z ^ a)⁻¹ * (1 - p + p * z ^ b)) ^ m) := by
  refine (coin_le p hp0 hp1 m _).trans ?_
  have h1p : 0 ≤ 1 - p := by linarith
  have hnn : ∀ k ∈ Finset.range (m + 1),
      0 ≤ (if k ∈ A then (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0) := by
    intro k _
    split_ifs
    · positivity
    · exact le_rfl
  have hconv : ∑ k ∈ Finset.range (m + 1),
        (if k ∈ A then ENNReal.ofReal ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) else 0) =
      ENNReal.ofReal (∑ k ∈ Finset.range (m + 1),
        (if k ∈ A then (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0)) := by
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ A <;> simp [hk]
  rw [hconv]
  apply ENNReal.ofReal_le_ofReal
  have hz0 : 0 < z := by linarith
  have hbin : ((z ^ a)⁻¹ * (1 - p + p * z ^ b)) ^ m =
      ∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * ((z ^ (a * m))⁻¹ * (z ^ b) ^ k) := by
    rw [mul_pow, inv_pow, ← pow_mul]
    rw [add_comm (1 - p) (p * z ^ b), add_pow (p * z ^ b) (1 - p) m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]; ring
  rw [hbin]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k ∈ A
  · rw [if_pos hk]
    have : 1 ≤ (z ^ (a * m))⁻¹ * (z ^ b) ^ k := by
      have h2 : z ^ (a * m) ≤ (z ^ b) ^ k := by
        rw [← pow_mul]; exact pow_le_pow_right₀ hz (by have := hA k hk; omega)
      have h3 : 0 < z ^ (a * m) := by positivity
      rw [inv_mul_eq_div, one_le_div h3]; exact h2
    have hnn' : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by positivity
    nlinarith
  · rw [if_neg hk]
    have : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * ((z ^ (a * m))⁻¹ * (z ^ b) ^ k) := by
      positivity
    exact this

lemma coin_lower_gen (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (a b : ℕ) (A : Set ℕ) (hA : ∀ k ∈ A, b * k ≤ a * m) :
    (coin p m).toOuterMeasure A ≤
      ENNReal.ofReal ((z ^ a * (1 - p + p * (z ^ b)⁻¹)) ^ m) := by
  refine (coin_le p hp0 hp1 m _).trans ?_
  have h1p : 0 ≤ 1 - p := by linarith
  have hnn : ∀ k ∈ Finset.range (m + 1),
      0 ≤ (if k ∈ A then (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0) := by
    intro k _
    split_ifs
    · positivity
    · exact le_rfl
  have hconv : ∑ k ∈ Finset.range (m + 1),
        (if k ∈ A then ENNReal.ofReal ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) else 0) =
      ENNReal.ofReal (∑ k ∈ Finset.range (m + 1),
        (if k ∈ A then (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0)) := by
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ A <;> simp [hk]
  rw [hconv]
  apply ENNReal.ofReal_le_ofReal
  have hz0 : 0 < z := by linarith
  have hbin : (z ^ a * (1 - p + p * (z ^ b)⁻¹)) ^ m =
      ∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * (z ^ (a * m) * ((z ^ b)⁻¹) ^ k) := by
    rw [mul_pow, ← pow_mul]
    rw [add_comm (1 - p) (p * (z ^ b)⁻¹), add_pow (p * (z ^ b)⁻¹) (1 - p) m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]; ring
  rw [hbin]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k ∈ A
  · rw [if_pos hk]
    have : 1 ≤ z ^ (a * m) * ((z ^ b)⁻¹) ^ k := by
      have h2 : (z ^ b) ^ k ≤ z ^ (a * m) := by
        rw [← pow_mul]; exact pow_le_pow_right₀ hz (by have := hA k hk; omega)
      have h3 : 0 < (z ^ b) ^ k := by positivity
      rw [inv_pow, ← div_eq_mul_inv, one_le_div h3]; exact h2
    have hnn' : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by positivity
    nlinarith
  · rw [if_neg hk]
    have : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * (z ^ (a * m) * ((z ^ b)⁻¹) ^ k) := by
      positivity
    exact this

lemma pow_lt_delta (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 250 * Real.log δ⁻¹ ≤ (m : ℝ)) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 0.996) :
    c ^ m < δ := by
  have hlog : 0 < Real.log δ⁻¹ := Real.log_pos (one_lt_inv₀ hδ |>.mpr hδ1)
  have hm1 : m ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hm
    linarith
  calc c ^ m < (0.996 : ℝ) ^ m := pow_lt_pow_left₀ hc hc0 hm1
    _ ≤ (Real.exp (-(1 / 250))) ^ m := by
        apply pow_le_pow_left₀ (by norm_num)
        have := Real.add_one_le_exp (-(1 / 250 : ℝ))
        linarith
    _ = Real.exp (-((m : ℝ) / 250)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-Real.log δ⁻¹) := by apply Real.exp_le_exp.mpr; linarith
    _ = δ := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_inv]

lemma upper_tail (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 250 * Real.log δ⁻¹ ≤ (m : ℝ)) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 0.075) :
    (coin p m).toOuterMeasure {h : ℕ | 0.12 * (m : ℝ) ≤ (h : ℝ)} < ENNReal.ofReal δ := by
  have hp1 : p ≤ 1 := by linarith
  refine lt_of_le_of_lt (coin_upper_gen p hp0 hp1 m (1.02 : ℝ) (by norm_num) 3 25 _ ?_) ?_
  · intro k hk
    have : 0.12 * (m : ℝ) ≤ (k : ℝ) := hk
    have : (3 * m : ℝ) ≤ 25 * k := by linarith
    exact_mod_cast this
  · rw [ENNReal.ofReal_lt_ofReal_iff hδ]
    have hf0 : 0 ≤ ((1.02 : ℝ) ^ 3)⁻¹ * (1 - p + p * (1.02 : ℝ) ^ 25) := by
      have : 0 ≤ 1 - p := by linarith
      positivity
    refine pow_lt_delta δ hδ hδ1 m hm _ hf0 ?_
    have : (1 - p + p * (1.02 : ℝ) ^ 25) ≤ 1 - 0.075 + 0.075 * (1.02 : ℝ) ^ 25 := by
      have : (1 : ℝ) ≤ (1.02 : ℝ) ^ 25 := one_le_pow₀ (by norm_num)
      nlinarith
    calc ((1.02 : ℝ) ^ 3)⁻¹ * (1 - p + p * (1.02 : ℝ) ^ 25)
        ≤ ((1.02 : ℝ) ^ 3)⁻¹ * (1 - 0.075 + 0.075 * (1.02 : ℝ) ^ 25) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ < 0.996 := by norm_num

lemma lower_tail (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 250 * Real.log δ⁻¹ ≤ (m : ℝ)) (p : ℝ) (hp0 : 0.165 ≤ p) (hp1 : p ≤ 1) :
    (coin p m).toOuterMeasure {h : ℕ | (h : ℝ) ≤ 0.12 * (m : ℝ)} < ENNReal.ofReal δ := by
  refine lt_of_le_of_lt (coin_lower_gen p (by linarith) hp1 m (1.015 : ℝ) (by norm_num) 3 25 _ ?_) ?_
  · intro k hk
    have : (k : ℝ) ≤ 0.12 * (m : ℝ) := hk
    have : (25 * k : ℝ) ≤ 3 * m := by linarith
    exact_mod_cast this
  · rw [ENNReal.ofReal_lt_ofReal_iff hδ]
    have hq0 : (0 : ℝ) ≤ ((1.015 : ℝ) ^ 25)⁻¹ := by positivity
    have hq1 : ((1.015 : ℝ) ^ 25)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hf0 : 0 ≤ (1.015 : ℝ) ^ 3 * (1 - p + p * ((1.015 : ℝ) ^ 25)⁻¹) := by
      have : 0 ≤ p := by linarith
      have : 0 ≤ p * ((1.015 : ℝ) ^ 25)⁻¹ := by positivity
      have : p * ((1.015 : ℝ) ^ 25)⁻¹ ≤ p := by nlinarith
      have : 0 ≤ 1 - p + p * ((1.015 : ℝ) ^ 25)⁻¹ := by nlinarith
      positivity
    refine pow_lt_delta δ hδ hδ1 m hm _ hf0 ?_
    have : (1 - p + p * ((1.015 : ℝ) ^ 25)⁻¹) ≤ 1 - 0.165 + 0.165 * ((1.015 : ℝ) ^ 25)⁻¹ := by
      nlinarith
    calc (1.015 : ℝ) ^ 3 * (1 - p + p * ((1.015 : ℝ) ^ 25)⁻¹)
        ≤ (1.015 : ℝ) ^ 3 * (1 - 0.165 + 0.165 * ((1.015 : ℝ) ^ 25)⁻¹) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ < 0.996 := by norm_num

theorem solution (θmin θmax θ γ δ : ℝ) (hθmin : 0 < θmin) (hlo : θmin ≤ θ) (hhi : θ ≤ θmax)
    (hθmax : θmax ≤ 0.002) (hmax : θmax = (1 + γ) * θmin) (hγ : 0 < γ) (hγ1 : γ ≤ 0.7)
    (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : 250 * Real.log δ⁻¹ ≤ (m : ℝ)) :
    Odd (rotR θmin θmax) ∧ 1 ≤ rotR θmin θmax ∧ (rotR θmin θmax : ℝ) ≤ 5 / (γ * θ) ∧
      (coin (Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2) m).toOuterMeasure
          {h : ℕ | ¬ (if 0.12 * (m : ℝ) < (h : ℝ) then
                        θmax / (1 + 0.9 * γ) ≤ θ ∧ θ ≤ θmax
                      else θmin ≤ θ ∧ θ ≤ (1 + 0.9 * γ) * θmin)} < ENNReal.ofReal δ ∧
      (coin (Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2) m).toOuterMeasure
          {h : ℕ | ¬ (if 0.12 * (m : ℝ) ≤ (h : ℝ) then
                        θmax / (1 + 0.9 * γ) ≤ θ ∧ θ ≤ θmax
                      else θmin ≤ θ ∧ θ ≤ (1 + 0.9 * γ) * θmin)} < ENNReal.ofReal δ := by
  obtain ⟨hA, hB, hθ, hd, hr⟩ := rot_facts θmin θmax γ hθmin hγ hγ1 hmax hθmax
  have hu : 0 < 1 + 0.9 * γ := by linarith
  have hpos : 0 < rotR θmin θmax := by exact_mod_cast hr
  refine ⟨⟨_, rfl⟩, by omega, ?_, ?_⟩
  · -- size bound
    have hθθ : 0 < θ := by linarith
    rw [le_div_iff₀ (by positivity)]
    have hdb := abs_le.mp hd
    have hpi := Real.pi_lt_d4
    have hpi0 := Real.pi_pos
    set r : ℝ := (rotR θmin θmax : ℝ) with hr'
    set k : ℝ := (rotK θmin θmax : ℝ) with hk
    have h1 : r * θmin ≤ Real.pi * k + θmin := by linarith [hdb.2]
    have hθ2 : θmin ≤ 0.002 := by nlinarith
    have h2 : r * (γ * θ) ≤ r * (γ * ((1 + γ) * θmin)) := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      apply mul_le_mul_of_nonneg_left _ hγ.le
      rw [← hmax]; exact hhi
    have h3 : r * (γ * ((1 + γ) * θmin)) = γ * (1 + γ) * (r * θmin) := by ring
    have h4 : γ * (1 + γ) * (r * θmin) ≤ γ * (1 + γ) * (Real.pi * k + θmin) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : Real.pi * (γ * k) ≤ Real.pi * (0.5 + γ / 2) := mul_le_mul_of_nonneg_left hB hpi0.le
    have h6 : Real.pi * (0.5 + γ / 2) * (1 + γ) ≤ 3.1416 * 0.5 * 1.7 * 1.7 := by
      have : Real.pi * (0.5 + γ / 2) * (1 + γ) = Real.pi * (1 + γ) ^ 2 / 2 := by ring
      rw [this]
      have : (1 + γ) ^ 2 ≤ 1.7 ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      nlinarith
    have h7 : γ * (1 + γ) * (Real.pi * k + θmin) =
        (1 + γ) * (Real.pi * (γ * k)) + γ * ((1 + γ) * θmin) := by ring
    have h8 : (1 + γ) * (Real.pi * (γ * k)) ≤ (1 + γ) * (Real.pi * (0.5 + γ / 2)) :=
      mul_le_mul_of_nonneg_left h5 (by linarith)
    nlinarith
  · -- tails
    have hsin_le : Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2 ≤ 1 := Real.sin_sq_le_one _
    have hsin0 : 0 ≤ Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2 := by positivity
    have hbd : θmax / (1 + 0.9 * γ) ≤ (1 + 0.9 * γ) * θmin := by
      rw [div_le_iff₀ hu, hmax]
      nlinarith [mul_pos hγ hθmin, mul_pos (mul_pos hγ hγ) hθmin]
    by_cases hz : θ ≤ θmax / (1 + 0.9 * γ)
    · -- lower zone
      obtain ⟨_, _, hs⟩ := low_zone θmin θmax γ θ hθmin hγ hγ1 hmax hθmax hlo hz
      have hBB : θmin ≤ θ ∧ θ ≤ (1 + 0.9 * γ) * θmin := ⟨hlo, hz.trans hbd⟩
      have hup := upper_tail δ hδ hδ1 m hm _ hsin0 hs
      constructor
      · refine lt_of_le_of_lt (OuterMeasure.mono _ ?_) hup
        intro h hh
        simp only [Set.mem_setOf_eq] at hh ⊢
        by_contra hn
        apply hh
        rw [if_neg (fun hc => hn (le_of_lt hc))]
        exact hBB
      · refine lt_of_le_of_lt (OuterMeasure.mono _ ?_) hup
        intro h hh
        simp only [Set.mem_setOf_eq] at hh ⊢
        by_contra hn
        apply hh
        rw [if_neg hn]
        exact hBB
    · push_neg at hz
      have hAA : θmax / (1 + 0.9 * γ) ≤ θ ∧ θ ≤ θmax := ⟨hz.le, hhi⟩
      by_cases hz2 : θ ≤ (1 + 0.9 * γ) * θmin
      · have hBB : θmin ≤ θ ∧ θ ≤ (1 + 0.9 * γ) * θmin := ⟨hlo, hz2⟩
        have hz0 : (0 : ENNReal) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
        have hsub : ∀ c : Prop, ∀ [Decidable c],
            ¬ (if c then (θmax / (1 + 0.9 * γ) ≤ θ ∧ θ ≤ θmax)
              else (θmin ≤ θ ∧ θ ≤ (1 + 0.9 * γ) * θmin)) → False := by
          intro c _ hh
          by_cases hc : c
          · rw [if_pos hc] at hh; exact hh hAA
          · rw [if_neg hc] at hh; exact hh hBB
        constructor
        · refine lt_of_le_of_lt (OuterMeasure.mono _ (?_ : _ ⊆ (∅ : Set ℕ))) ?_
          · intro h hh
            exact (hsub _ hh).elim
          · rw [OuterMeasure.empty]; exact hz0
        · refine lt_of_le_of_lt (OuterMeasure.mono _ (?_ : _ ⊆ (∅ : Set ℕ))) ?_
          · intro h hh
            exact (hsub _ hh).elim
          · rw [OuterMeasure.empty]; exact hz0
      · push_neg at hz2
        obtain ⟨_, _, hs⟩ := high_zone θmin θmax γ θ hθmin hγ hγ1 hmax hθmax
          (by rw [mul_comm]; exact hz2.le) hhi
        have hlow := lower_tail δ hδ hδ1 m hm _ hs hsin_le
        constructor
        · refine lt_of_le_of_lt (OuterMeasure.mono _ ?_) hlow
          intro h hh
          simp only [Set.mem_setOf_eq] at hh ⊢
          by_contra hn
          apply hh
          rw [if_pos (lt_of_not_ge hn)]
          exact hAA
        · refine lt_of_le_of_lt (OuterMeasure.mono _ ?_) hlow
          intro h hh
          simp only [Set.mem_setOf_eq] at hh ⊢
          by_contra hn
          apply hh
          rw [if_pos (le_of_lt (lt_of_not_ge hn))]
          exact hAA
