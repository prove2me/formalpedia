-- Prove2me | solution 1 for QApproxCount.Counting.eqs_15_28
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:55:09.700989+00:00
-- url     : https://prove2.me/submissions/9da9e533-99d7-42c6-90e8-9db81b33dd06

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


lemma coin_upper (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (coin p m).toOuterMeasure {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)} ≤
      ENNReal.ofReal (((z ^ 19)⁻¹ * (1 - p + p * z ^ 20)) ^ m) := by
  refine (coin_le p hp0 hp1 m _).trans ?_
  have h1p : 0 ≤ 1 - p := by linarith
  have hnn : ∀ k ∈ Finset.range (m + 1),
      0 ≤ (if k ∈ {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)} then
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0) := by
    intro k _
    split_ifs
    · positivity
    · exact le_rfl
  have hconv : ∑ k ∈ Finset.range (m + 1),
        (if k ∈ {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)} then
          ENNReal.ofReal ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) else 0) =
      ENNReal.ofReal (∑ k ∈ Finset.range (m + 1),
        (if k ∈ {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)} then
          (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0)) := by
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)} <;> simp [hk]
  rw [hconv]
  apply ENNReal.ofReal_le_ofReal
  have hz0 : 0 < z := by linarith
  have hbin : ((z ^ 19)⁻¹ * (1 - p + p * z ^ 20)) ^ m =
      ∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * ((z ^ (19 * m))⁻¹ * (z ^ 20) ^ k) := by
    rw [mul_pow, inv_pow, ← pow_mul]
    rw [add_comm (1 - p) (p * z ^ 20), add_pow (p * z ^ 20) (1 - p) m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]; ring
  rw [hbin]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k ∈ {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)}
  · rw [if_pos hk]
    have hk' : 19 * m ≤ 20 * k := by
      have : 0.95 * (m : ℝ) ≤ (k : ℝ) := hk
      have : (19 * m : ℝ) ≤ 20 * k := by linarith
      exact_mod_cast this
    have : 1 ≤ (z ^ (19 * m))⁻¹ * (z ^ 20) ^ k := by
      have h2 : z ^ (19 * m) ≤ (z ^ 20) ^ k := by
        rw [← pow_mul]; exact pow_le_pow_right₀ hz (by omega)
      have h3 : 0 < z ^ (19 * m) := by positivity
      rw [inv_mul_eq_div, one_le_div h3]; exact h2
    have hnn' : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by positivity
    nlinarith
  · rw [if_neg hk]
    have : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * ((z ^ (19 * m))⁻¹ * (z ^ 20) ^ k) := by
      positivity
    exact this

/-- per-round factor bound -/
lemma factor_bound (j : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp : p * ((1.05 : ℝ) ^ j) ^ 2 ≤ 0.81) :
    (((1.08 * 1.02 ^ j : ℝ) ^ 19)⁻¹ * (1 - p + p * (1.08 * 1.02 ^ j : ℝ) ^ 20)) ≤
      0.97 * (0.926 : ℝ) ^ (j - 1) := by
  have hz : ((1.08 * 1.02 ^ j : ℝ) ^ 19)⁻¹ * (1 - p + p * (1.08 * 1.02 ^ j : ℝ) ^ 20) =
      ((1.08 * 1.02 ^ j : ℝ) ^ 19)⁻¹ * (1 - p) + p * (1.08 * 1.02 ^ j : ℝ) := by
    have : (1.08 * 1.02 ^ j : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hz]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [pow_zero, mul_one, Nat.zero_sub] at hp ⊢
    have : (0.81 : ℝ) = 0.81 := rfl
    have hk : (1.08 ^ 19 : ℝ)⁻¹ * (1 - p) + p * 1.08 ≤
        (1.08 ^ 19 : ℝ)⁻¹ * (1 - 0.81) + 0.81 * 1.08 := by
      have h19 : ((1.08 : ℝ) ^ 19)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      have h19' : ((1.08 : ℝ) ^ 19)⁻¹ ≤ 1.08 := by linarith
      nlinarith
    refine hk.trans ?_
    norm_num
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    set a : ℝ := ((1.02 : ℝ) ^ 19)⁻¹ with ha
    set σ : ℝ := 1.02 / 1.1025 with hσ
    have ha1 : a ≤ 0.926 := by rw [ha]; norm_num
    have hσ1 : σ ≤ 0.926 := by rw [hσ]; norm_num
    have ha0 : 0 ≤ a := by positivity
    have hσ0 : 0 ≤ σ := by positivity
    have e1 : ((1.08 * 1.02 ^ (i + 1) : ℝ) ^ 19)⁻¹ = ((1.08 : ℝ) ^ 19)⁻¹ * a ^ (i + 1) := by
      rw [ha, mul_pow, ← pow_mul, mul_comm (i + 1) 19, pow_mul, mul_inv, inv_pow]
    have hw : (0 : ℝ) < ((1.05 : ℝ) ^ (i + 1)) ^ 2 := by positivity
    have e2 : p * (1.02 : ℝ) ^ (i + 1) ≤ 0.81 * σ ^ (i + 1) := by
      have h1 : p ≤ 0.81 / ((1.05 : ℝ) ^ (i + 1)) ^ 2 := by rw [le_div_iff₀ hw]; exact hp
      have h2 : (0.81 : ℝ) / ((1.05 : ℝ) ^ (i + 1)) ^ 2 * (1.02 : ℝ) ^ (i + 1) = 0.81 * σ ^ (i + 1) := by
        rw [hσ, div_pow, ← pow_mul, mul_comm (i + 1) 2, pow_mul]
        norm_num
        field_simp
      calc p * (1.02 : ℝ) ^ (i + 1) ≤ 0.81 / ((1.05 : ℝ) ^ (i + 1)) ^ 2 * (1.02 : ℝ) ^ (i + 1) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := h2
    have e3 : a ^ (i + 1) ≤ a * 0.926 ^ i := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 ha1 i) ha0
    have e4 : σ ^ (i + 1) ≤ σ * 0.926 ^ i := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσ0 hσ1 i) hσ0
    have hinv : 0 ≤ ((1.08 : ℝ) ^ 19)⁻¹ := by positivity
    have hpa : 0 ≤ ((1.08 : ℝ) ^ 19)⁻¹ * a ^ (i + 1) := by positivity
    have hz0 : 0 ≤ ((1.08 * 1.02 ^ (i + 1) : ℝ) ^ 19)⁻¹ * p := by positivity
    have step1 : ((1.08 * 1.02 ^ (i + 1) : ℝ) ^ 19)⁻¹ * (1 - p) + p * (1.08 * 1.02 ^ (i + 1) : ℝ) ≤
        ((1.08 : ℝ) ^ 19)⁻¹ * a ^ (i + 1) + 1.08 * (p * (1.02 : ℝ) ^ (i + 1)) := by
      rw [e1] at hz0 ⊢
      nlinarith
    have step2 : ((1.08 : ℝ) ^ 19)⁻¹ * a ^ (i + 1) + 1.08 * (p * (1.02 : ℝ) ^ (i + 1)) ≤
        ((1.08 : ℝ) ^ 19)⁻¹ * (a * 0.926 ^ i) + 1.08 * (0.81 * (σ * 0.926 ^ i)) := by
      have h1 : ((1.08 : ℝ) ^ 19)⁻¹ * a ^ (i + 1) ≤ ((1.08 : ℝ) ^ 19)⁻¹ * (a * 0.926 ^ i) :=
        mul_le_mul_of_nonneg_left e3 hinv
      have h2 : p * (1.02 : ℝ) ^ (i + 1) ≤ 0.81 * (σ * 0.926 ^ i) :=
        e2.trans (mul_le_mul_of_nonneg_left e4 (by norm_num))
      nlinarith
    refine step1.trans (step2.trans ?_)
    have : ((1.08 : ℝ) ^ 19)⁻¹ * a + 1.08 * (0.81 * σ) ≤ 0.97 := by rw [ha, hσ]; norm_num
    have hp' : (0 : ℝ) ≤ 0.926 ^ i := by positivity
    nlinarith

lemma G_sum (m : ℕ) (hm : 1 ≤ m) (k₀ : ℕ) :
    ∑ j ∈ Finset.range (k₀ + 1), (0.97 * (0.926 : ℝ) ^ (j - 1)) ^ m ≤ 15 * (0.97 : ℝ) ^ m := by
  rw [Finset.sum_range_succ']
  have hx0 : (0 : ℝ) ≤ 0.926 ^ m := by positivity
  have hx1 : (0.926 : ℝ) ^ m ≤ 0.926 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have h1 : ∀ i ∈ Finset.range k₀, (0.97 * (0.926 : ℝ) ^ (i + 1 - 1)) ^ m =
      (0.97 : ℝ) ^ m * ((0.926 : ℝ) ^ m) ^ i := by
    intro i _
    simp only [Nat.add_sub_cancel]
    rw [mul_pow, ← pow_mul, ← pow_mul]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have hgeom : ∑ i ∈ Finset.range k₀, ((0.926 : ℝ) ^ m) ^ i ≤ 14 := by
    have h := geom_sum_mul ((0.926 : ℝ) ^ m) k₀
    have hpow : ((0.926 : ℝ) ^ m) ^ k₀ ≥ 0 := by positivity
    have hS : 0 ≤ ∑ i ∈ Finset.range k₀, ((0.926 : ℝ) ^ m) ^ i := by positivity
    nlinarith
  have : (0.97 * (0.926 : ℝ) ^ (0 - 1)) ^ m = 0.97 ^ m := by norm_num
  rw [this]
  have hp : (0 : ℝ) ≤ 0.97 ^ m := by positivity
  nlinarith

theorem solution (θ δ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 0.001) (k₀ : ℕ)
    (hk₀ : θ * (1.05 : ℝ) ^ k₀ ≤ 0.9) (hk₀max : 0.9 < θ * (1.05 : ℝ) ^ (k₀ + 1))
    (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : 5000 * Real.log (5 / δ) ≤ (m : ℝ)) :
    ∑ k ∈ Finset.range (k₀ + 1),
        (coin (Real.sin ((oddFloor k : ℝ) * θ) ^ 2) m).toOuterMeasure
          {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)} ≤ ENNReal.ofReal (δ / 4) := by
  -- per-term bound
  have hterm : ∀ k ∈ Finset.range (k₀ + 1),
      (coin (Real.sin ((oddFloor k : ℝ) * θ) ^ 2) m).toOuterMeasure
          {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)} ≤
        ENNReal.ofReal ((0.97 * (0.926 : ℝ) ^ (k₀ - k - 1)) ^ m) := by
    intro k hk
    have hkk : k ≤ k₀ := by simpa [Nat.lt_succ_iff] using hk
    obtain ⟨j, hj⟩ : ∃ j, k₀ = k + j := ⟨k₀ - k, by omega⟩
    have hjk : k₀ - k = j := by omega
    rw [hjk]
    set p : ℝ := Real.sin ((oddFloor k : ℝ) * θ) ^ 2 with hp
    have hp0 : 0 ≤ p := by positivity
    have hp1 : p ≤ 1 := Real.sin_sq_le_one _
    have hz : (1 : ℝ) ≤ 1.08 * 1.02 ^ j := by
      have : (1 : ℝ) ≤ 1.02 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    refine (coin_upper p hp0 hp1 m _ hz).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hf0 : 0 ≤ (((1.08 * 1.02 ^ j : ℝ) ^ 19)⁻¹ * (1 - p + p * (1.08 * 1.02 ^ j : ℝ) ^ 20)) := by
      have : 0 ≤ 1 - p := by linarith
      have h20 : 0 ≤ p * (1.08 * 1.02 ^ j : ℝ) ^ 20 := by positivity
      have : 0 ≤ 1 - p + p * (1.08 * 1.02 ^ j : ℝ) ^ 20 := by linarith
      positivity
    refine pow_le_pow_left₀ hf0 (factor_bound j p hp0 ?_) m
    -- p * (1.05^j)^2 ≤ 0.81
    obtain ⟨hr1, _⟩ := oddFloor_bounds k
    have hu0 : 0 ≤ (oddFloor k : ℝ) * θ := by positivity
    have hu1 : (oddFloor k : ℝ) * θ * (1.05 : ℝ) ^ j ≤ 0.9 := by
      have h1 : (oddFloor k : ℝ) * θ ≤ (1.05 : ℝ) ^ k * θ := mul_le_mul_of_nonneg_right hr1 hθ.le
      have h2 : (1.05 : ℝ) ^ k * θ * (1.05 : ℝ) ^ j = θ * (1.05 : ℝ) ^ k₀ := by
        rw [hj, pow_add]; ring
      calc (oddFloor k : ℝ) * θ * (1.05 : ℝ) ^ j ≤ (1.05 : ℝ) ^ k * θ * (1.05 : ℝ) ^ j :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = θ * (1.05 : ℝ) ^ k₀ := h2
        _ ≤ 0.9 := hk₀
    have hsq : p ≤ ((oddFloor k : ℝ) * θ) ^ 2 := Real.sin_sq_le_sq
    have hw : (0 : ℝ) ≤ ((1.05 : ℝ) ^ j) ^ 2 := by positivity
    calc p * ((1.05 : ℝ) ^ j) ^ 2 ≤ ((oddFloor k : ℝ) * θ) ^ 2 * ((1.05 : ℝ) ^ j) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq hw
      _ = ((oddFloor k : ℝ) * θ * (1.05 : ℝ) ^ j) ^ 2 := by ring
      _ ≤ 0.9 ^ 2 := pow_le_pow_left₀ (by positivity) hu1 2
      _ = 0.81 := by norm_num
  have hlog : (1 : ℝ) ≤ Real.log (5 / δ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    rw [le_div_iff₀ hδ]
    nlinarith
  have hm5 : (5000 : ℝ) ≤ m := by linarith
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hrefl : ∑ k ∈ Finset.range (k₀ + 1), (0.97 * (0.926 : ℝ) ^ (k₀ - k - 1)) ^ m =
      ∑ j ∈ Finset.range (k₀ + 1), (0.97 * (0.926 : ℝ) ^ (j - 1)) ^ m := by
    rw [← Finset.sum_range_reflect (fun j => (0.97 * (0.926 : ℝ) ^ (j - 1)) ^ m) (k₀ + 1)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k₀ + 1 - 1 - k = k₀ - k := by omega
    simp only [this]
  rw [hrefl]
  refine (G_sum m hm1 k₀).trans ?_
  -- final numerics
  have he1 : (0.97 : ℝ) ≤ Real.exp (-0.03) := by
    have := Real.add_one_le_exp (-0.03 : ℝ)
    linarith
  have hE : Real.exp (-(0.015 * (m : ℝ))) ≤ δ / 5 := by
    calc Real.exp (-(0.015 * (m : ℝ))) ≤ Real.exp (-Real.log (5 / δ)) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = δ / 5 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hE2 : Real.exp (-(0.015 * (m : ℝ))) ≤ 1 / 76 := by
    have h75 : (76 : ℝ) ≤ Real.exp (0.015 * m) := by
      have := Real.add_one_le_exp (0.015 * (m : ℝ))
      linarith
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h75
  have hE0 : 0 ≤ Real.exp (-(0.015 * (m : ℝ))) := (Real.exp_pos _).le
  have hpow : (0.97 : ℝ) ^ m ≤ Real.exp (-(0.015 * (m : ℝ))) * Real.exp (-(0.015 * (m : ℝ))) := by
    calc (0.97 : ℝ) ^ m ≤ (Real.exp (-0.03)) ^ m := pow_le_pow_left₀ (by norm_num) he1 m
      _ = Real.exp (-(0.015 * (m : ℝ))) * Real.exp (-(0.015 * (m : ℝ))) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hprod : Real.exp (-(0.015 * (m : ℝ))) * Real.exp (-(0.015 * (m : ℝ))) ≤ δ / 5 * (1 / 76) :=
    mul_le_mul hE hE2 hE0 (by positivity)
  nlinarith
