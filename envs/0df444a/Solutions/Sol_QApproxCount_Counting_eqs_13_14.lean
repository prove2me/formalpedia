-- Prove2me | solution 1 for QApproxCount.Counting.eqs_13_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:19:00.508157+00:00
-- url     : https://prove2.me/submissions/b102b9e3-e325-4baf-bbb9-5c20b4784aa2

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

theorem solution (p : ℝ) (hp : 0 < p) (hp95 : p < 0.95) (m : ℕ) :
    (coin p m).toOuterMeasure {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) *
        (0.95 * Real.log (0.95 / p) + (1 - 0.95) * Real.log ((1 - 0.95) / (1 - p)))))) := by
  have hp1 : p ≤ 1 := by linarith
  refine (coin_le p hp.le hp1 m _).trans ?_
  set x : ℝ := 0.95 * (1 - p) / (0.05 * p) with hx
  have h1p : 0 < 1 - p := by linarith
  have hxpos : 0 < x := by rw [hx]; apply div_pos <;> nlinarith
  have hx1 : 1 ≤ x := by
    rw [hx, le_div_iff₀ (by nlinarith)]; nlinarith
  set l : ℝ := Real.log x with hl
  have hl0 : 0 ≤ l := Real.log_nonneg hx1
  have hel : Real.exp l = x := Real.exp_log hxpos
  have hsum := tail_sum_le p hp.le hp1 m (0.95 * (m : ℝ)) l hl0
  rw [hel] at hsum
  have h20 : 1 - p + p * x = 20 * (1 - p) := by
    rw [hx]; field_simp; ring
  rw [h20] at hsum
  have hrhs : Real.exp (-(l * (0.95 * (m : ℝ)))) * (20 * (1 - p)) ^ m =
      Real.exp (-((m : ℝ) *
        (0.95 * Real.log (0.95 / p) + (1 - 0.95) * Real.log ((1 - 0.95) / (1 - p))))) := by
    have e1 : (20 * (1 - p)) ^ m = Real.exp ((m : ℝ) * Real.log (20 * (1 - p))) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
    rw [e1, ← Real.exp_add]
    congr 1
    have hl' : l = Real.log 0.95 + Real.log (1 - p) - Real.log 0.05 - Real.log p := by
      rw [hl, hx, Real.log_div (by nlinarith) (by nlinarith), Real.log_mul (by norm_num) h1p.ne',
        Real.log_mul (by norm_num) hp.ne']
      ring
    have h20' : Real.log (20 * (1 - p)) = - Real.log 0.05 + Real.log (1 - p) := by
      rw [Real.log_mul (by norm_num) h1p.ne']
      have : Real.log (20 : ℝ) + Real.log 0.05 = 0 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
      linarith
    have hA : Real.log (0.95 / p) = Real.log 0.95 - Real.log p :=
      Real.log_div (by norm_num) hp.ne'
    have hB : Real.log ((1 - 0.95) / (1 - p)) = Real.log 0.05 - Real.log (1 - p) := by
      rw [Real.log_div (by norm_num) h1p.ne']; norm_num
    rw [hl', h20', hA, hB]
    ring
  rw [hrhs] at hsum
  have hnn : ∀ k ∈ Finset.range (m + 1),
      0 ≤ (if 0.95 * (m : ℝ) ≤ (k : ℝ) then (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0) := by
    intro k _
    split_ifs
    · have : 0 ≤ 1 - p := by linarith
      positivity
    · exact le_rfl
  have hconv : ∑ k ∈ Finset.range (m + 1),
        (if k ∈ {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)} then
          ENNReal.ofReal ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) else 0) =
      ENNReal.ofReal (∑ k ∈ Finset.range (m + 1),
        (if 0.95 * (m : ℝ) ≤ (k : ℝ) then (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0)) := by
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : 0.95 * (m : ℝ) ≤ (k : ℝ) <;> simp [hk]
  rw [hconv]
  exact ENNReal.ofReal_le_ofReal hsum
