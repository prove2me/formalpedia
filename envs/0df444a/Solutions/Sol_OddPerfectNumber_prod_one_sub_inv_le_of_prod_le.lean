-- Prove2me | solution 1 for OddPerfectNumber.prod_one_sub_inv_le_of_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-08T06:56:56.413071+00:00
-- url     : https://prove2.me/submissions/83c982b8-e801-452d-9629-5f49789e6a8c

import Mathlib

open Finset

/-- Abel summation: if `c` is nonnegative and non-increasing on `range n`, and every partial
sum of `e` over `range m` (`m ≤ n`) is nonpositive, then `∑ c i * e i ≤ 0`. -/
theorem sum_mul_nonpos_of_partial_sums_nonpos (n : ℕ) (c e : ℕ → ℝ)
    (hc0 : ∀ i < n, 0 ≤ c i)
    (hcmono : ∀ i, i + 1 < n → c (i + 1) ≤ c i)
    (hE : ∀ m ≤ n, ∑ i ∈ range m, e i ≤ 0) :
    ∑ i ∈ range n, c i * e i ≤ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Finset.sum_range_by_parts c e n
  simp only [smul_eq_mul] at h
  rw [h]
  have h1 : c (n - 1) * ∑ i ∈ range n, e i ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hc0 _ (by omega)) (hE n le_rfl)
  have h2 : 0 ≤ ∑ i ∈ range (n - 1), (c (i + 1) - c i) * ∑ j ∈ range (i + 1), e j := by
    refine Finset.sum_nonneg fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hi' : i + 1 < n := by omega
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hcmono i hi']) (hE (i + 1) (by omega))
  linarith

/-- The tangent-line (concavity) inequality for `t ↦ log (1 - e⁻ᵗ)`, written multiplicatively:
for `x, y > 1`, `log (1 - 1/x) - log (1 - 1/y) ≤ (log x - log y) / (y - 1)`. -/
theorem log_one_sub_inv_sub_le {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    Real.log (1 - 1 / x) - Real.log (1 - 1 / y) ≤ (Real.log x - Real.log y) / (y - 1) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hy0 : (0:ℝ) < y := by linarith
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hyne : y ≠ 0 := ne_of_gt hy0
  have hy1 : (0:ℝ) < y - 1 := by linarith
  have hax : 0 < 1 - 1 / x := by
    have : 1 / x < 1 := by rw [div_lt_one hx0]; exact hx
    linarith
  have hay : 0 < 1 - 1 / y := by
    have : 1 / y < 1 := by rw [div_lt_one hy0]; exact hy
    linarith
  have hA : 0 < (1 - 1 / x) / (1 - 1 / y) := div_pos hax hay
  have s1 : Real.log (1 - 1 / x) - Real.log (1 - 1 / y) ≤ (1 - 1 / x) / (1 - 1 / y) - 1 := by
    have := Real.log_le_sub_one_of_pos hA
    rwa [Real.log_div (ne_of_gt hax) (ne_of_gt hay)] at this
  have s2 : (1 - 1 / x) / (1 - 1 / y) - 1 = (x - y) / (x * (y - 1)) := by
    rw [div_sub_one (ne_of_gt hay)]
    field_simp
    ring
  have s3 : 1 - y / x ≤ Real.log x - Real.log y := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < y / x from div_pos hy0 hx0)
    rw [Real.log_div hyne hxne] at h
    linarith
  have s4 : (x - y) / (x * (y - 1)) ≤ (Real.log x - Real.log y) / (y - 1) := by
    rw [div_le_div_iff₀ (by positivity) hy1]
    have hxy : (x - y) * (y - 1) = (1 - y / x) * (x * (y - 1)) := by field_simp
    rw [hxy]
    exact mul_le_mul_of_nonneg_right s3 (by positivity)
  linarith [s1.trans (le_of_eq s2)]

/-- **Nielsen 2015, Lemma 1.2.**  If `y` is non-decreasing, all `x i, y i > 1`, and every partial
product of `x` is at most the corresponding partial product of `y`, then
`∏ (1 - 1/x i) ≤ ∏ (1 - 1/y i)`. -/
theorem solution (n : ℕ) (x y : ℕ → ℝ)
    (hx : ∀ i < n, 1 < x i) (hy : ∀ i < n, 1 < y i)
    (hymono : ∀ i, i + 1 < n → y i ≤ y (i + 1))
    (hle : ∀ m ≤ n, ∏ i ∈ range m, x i ≤ ∏ i ∈ range m, y i) :
    ∏ i ∈ range n, (1 - 1 / x i) ≤ ∏ i ∈ range n, (1 - 1 / y i) := by
  have hxpos : ∀ i < n, (0:ℝ) < x i := fun i hi => lt_trans one_pos (hx i hi)
  have hypos : ∀ i < n, (0:ℝ) < y i := fun i hi => lt_trans one_pos (hy i hi)
  have hax : ∀ i < n, (0:ℝ) < 1 - 1 / x i := by
    intro i hi
    have h1 : 1 / x i < 1 := by rw [div_lt_one (hxpos i hi)]; exact hx i hi
    linarith
  have hay : ∀ i < n, (0:ℝ) < 1 - 1 / y i := by
    intro i hi
    have h1 : 1 / y i < 1 := by rw [div_lt_one (hypos i hi)]; exact hy i hi
    linarith
  have hlogsum :
      ∑ i ∈ range n, Real.log (1 - 1 / x i) ≤ ∑ i ∈ range n, Real.log (1 - 1 / y i) := by
    have key : ∑ i ∈ range n, (Real.log (1 - 1 / x i) - Real.log (1 - 1 / y i))
        ≤ ∑ i ∈ range n, 1 / (y i - 1) * (Real.log (x i) - Real.log (y i)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [mem_range] at hi
      rw [one_div_mul_eq_div]
      exact log_one_sub_inv_sub_le (hx i hi) (hy i hi)
    have habel : ∑ i ∈ range n, 1 / (y i - 1) * (Real.log (x i) - Real.log (y i)) ≤ 0 := by
      refine sum_mul_nonpos_of_partial_sums_nonpos n (fun i => 1 / (y i - 1))
        (fun i => Real.log (x i) - Real.log (y i)) ?_ ?_ ?_
      · intro i hi
        have h2 : (0:ℝ) < y i - 1 := by linarith [hy i hi]
        positivity
      · intro i hi
        have h1 : y i ≤ y (i + 1) := hymono i hi
        have h2 : 1 < y i := hy i (by omega)
        exact one_div_le_one_div_of_le (by linarith) (by linarith)
      · intro m hm
        have hxm : ∀ i ∈ range m, x i ≠ 0 := fun i hi => by
          rw [mem_range] at hi; exact ne_of_gt (hxpos i (by omega))
        have hym : ∀ i ∈ range m, y i ≠ 0 := fun i hi => by
          rw [mem_range] at hi; exact ne_of_gt (hypos i (by omega))
        rw [Finset.sum_sub_distrib, ← Real.log_prod hxm, ← Real.log_prod hym, sub_nonpos]
        refine Real.log_le_log ?_ (hle m hm)
        exact Finset.prod_pos fun i hi => hxpos i (by rw [mem_range] at hi; omega)
    rw [Finset.sum_sub_distrib] at key
    linarith
  have hexpx :
      ∏ i ∈ range n, (1 - 1 / x i) = Real.exp (∑ i ∈ range n, Real.log (1 - 1 / x i)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun i hi =>
      (Real.exp_log (hax i (by rw [mem_range] at hi; omega))).symm
  have hexpy :
      ∏ i ∈ range n, (1 - 1 / y i) = Real.exp (∑ i ∈ range n, Real.log (1 - 1 / y i)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun i hi =>
      (Real.exp_log (hay i (by rw [mem_range] at hi; omega))).symm
  rw [hexpx, hexpy]
  exact Real.exp_le_exp.mpr hlogsum

