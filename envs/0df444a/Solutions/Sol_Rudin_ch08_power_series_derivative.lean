-- Prove2me | solution 1 for Rudin.ch08_power_series_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T21:39:26.59361+00:00
-- url     : https://prove2.me/submissions/ecb86095-3985-4944-9714-6b5abcd65449

import Mathlib
import Definitions.Def_Rudin_ch03_series

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace RudinLoc81

open Filter Topology Rudin

/-- Terms of a convergent series tend to zero. -/
theorem term_tendsto_zero {a : ℕ → ℝ} (h : SeriesConverges a) :
    Tendsto a atTop (𝓝 0) := by
  obtain ⟨s, hs⟩ := h
  have h1 : Tendsto (fun n => partialSum a (n + 1)) atTop (𝓝 s) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have h2 : ∀ n, a n = partialSum a (n + 1) - partialSum a n := by
    intro n
    rw [partialSum, partialSum, Finset.sum_range_succ]
    ring
  have h3 : Tendsto (fun n => partialSum a (n + 1) - partialSum a n) atTop (𝓝 (s - s)) :=
    h1.sub hs
  rw [sub_self] at h3
  exact h3.congr (fun n => (h2 n).symm)

/-- Convergent series have bounded terms. -/
theorem exists_bound_of_converges {a : ℕ → ℝ} (h : SeriesConverges a) :
    ∃ M : ℝ, 0 < M ∧ ∀ n, |a n| ≤ M := by
  have h0 := (term_tendsto_zero h).abs
  simp only [abs_zero] at h0
  obtain ⟨M, hM⟩ := h0.bddAbove_range
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun n => ?_⟩
  exact le_trans (hM ⟨n, rfl⟩) (le_max_left _ _)


/-! ### Rudin, Theorem 8.1 -/

theorem rudin_8_1 (c : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hconv : ∀ x : ℝ, |x| < R → SeriesConverges (fun n => c n * x ^ n))
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, |x| < R → SeriesConvergesTo (fun n => c n * x ^ n) (f x))
    (g : ℝ → ℝ) (hg : ∀ x : ℝ, |x| < R →
      SeriesConvergesTo (fun n => (n : ℝ) * c n * x ^ (n - 1)) (g x)) :
    ∀ x : ℝ, |x| < R → HasDerivAt f (g x) x := by
  intro x hx
  obtain ⟨r, hxr, hrR⟩ := exists_between hx
  obtain ⟨ρ, hrρ, hρR⟩ := exists_between hrR
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  have hρ0 : 0 < ρ := hr0.trans hrρ
  -- coefficients are dominated on the circle of radius `ρ`
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_converges
    (hconv ρ (by rwa [abs_of_pos hρ0]))
  have hMc : ∀ n : ℕ, |c n| * ρ ^ n ≤ M := by
    intro n
    have := hM n
    rwa [abs_mul, abs_pow, abs_of_pos hρ0] at this
  have hq : |r / ρ| < 1 := by
    rw [abs_of_pos (by positivity)]
    rw [div_lt_one hρ0]
    exact hrρ
  set s : Set ℝ := Set.Ioo (-r) r with hs
  have hmemR : ∀ y ∈ s, |y| < R := by
    intro y hy
    have : |y| < r := abs_lt.2 ⟨hy.1, hy.2⟩
    linarith
  have hyr : ∀ y ∈ s, |y| ≤ r := fun y hy => le_of_lt (abs_lt.2 ⟨hy.1, hy.2⟩)
  -- domination of the series itself
  have hdom : ∀ (n : ℕ), ∀ y ∈ s, ‖c n * y ^ n‖ ≤ M * (r / ρ) ^ n := by
    intro n y hy
    rw [Real.norm_eq_abs, abs_mul, abs_pow, div_pow]
    have h1 : |y| ^ n ≤ r ^ n := pow_le_pow_left₀ (abs_nonneg y) (hyr y hy) n
    have h2 : |c n| * ρ ^ n ≤ M := hMc n
    have hρn : (0:ℝ) < ρ ^ n := by positivity
    have h3 : |c n| * |y| ^ n ≤ |c n| * r ^ n :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h4 : |c n| * r ^ n ≤ M * (r ^ n / ρ ^ n) := by
      rw [mul_div_assoc'] at *
      rw [le_div_iff₀ hρn]
      calc |c n| * r ^ n * ρ ^ n = (|c n| * ρ ^ n) * r ^ n := by ring
        _ ≤ M * r ^ n := mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  have hsumg : Summable (fun n : ℕ => M * (r / ρ) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) (by rwa [abs_of_pos (by positivity)] at hq)).mul_left M
  -- domination of the differentiated series
  have hdom' : ∀ (n : ℕ), ∀ y ∈ s,
      ‖(n : ℝ) * c n * y ^ (n - 1)‖ ≤ (M / r) * ((n : ℝ) * (r / ρ) ^ n) := by
    intro n y hy
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hc : |c (m + 1)| ≤ M / ρ ^ (m + 1) := by
        rw [le_div_iff₀ (by positivity)]
        exact hMc (m + 1)
      have h1 : |y| ^ m ≤ r ^ m := pow_le_pow_left₀ (abs_nonneg y) (hyr y hy) m
      have habs : |((m + 1 : ℕ) : ℝ)| = (m : ℝ) + 1 := by
        push_cast
        rw [abs_of_nonneg (by positivity)]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.add_sub_cancel, habs]
      push_cast
      have hid : ((m : ℝ) + 1) * (M / ρ ^ (m + 1)) * r ^ m
          = M / r * (((m : ℝ) + 1) * (r / ρ) ^ (m + 1)) := by
        rw [div_pow, pow_succ r m, pow_succ ρ m]
        field_simp
      calc ((m : ℝ) + 1) * |c (m + 1)| * |y| ^ m
          ≤ ((m : ℝ) + 1) * (M / ρ ^ (m + 1)) * r ^ m := by
            apply mul_le_mul _ h1 (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hc (by positivity)
        _ = M / r * (((m : ℝ) + 1) * (r / ρ) ^ (m + 1)) := hid
  have hsumg' : Summable (fun n : ℕ => (M / r) * ((n : ℝ) * (r / ρ) ^ n)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (by rwa [Real.norm_eq_abs])
    simpa using h.mul_left (M / r)
  -- identify the sums
  have hsf : ∀ y ∈ s, Summable (fun n : ℕ => c n * y ^ n) := fun y hy =>
    Summable.of_norm_bounded hsumg (fun n => hdom n y hy)
  have hsg : ∀ y ∈ s, Summable (fun n : ℕ => (n : ℝ) * c n * y ^ (n - 1)) := fun y hy =>
    Summable.of_norm_bounded hsumg' (fun n => hdom' n y hy)
  have htf : ∀ y ∈ s, (∑' n : ℕ, c n * y ^ n) = f y := by
    intro y hy
    exact tendsto_nhds_unique (hsf y hy).hasSum.tendsto_sum_nat (hf y (hmemR y hy))
  have htg : ∀ y ∈ s, (∑' n : ℕ, (n : ℝ) * c n * y ^ (n - 1)) = g y := by
    intro y hy
    exact tendsto_nhds_unique (hsg y hy).hasSum.tendsto_sum_nat (hg y (hmemR y hy))
  -- uniform convergence of the differentiated partial sums
  have huni : TendstoUniformlyOn
      (fun N : ℕ => fun y => ∑ n ∈ Finset.range N, (n : ℝ) * c n * y ^ (n - 1)) g atTop s := by
    refine TendstoUniformlyOn.congr_right (tendstoUniformlyOn_tsum_nat hsumg' hdom') ?_
    exact fun y hy => htg y hy
  -- each partial sum is a polynomial
  have hderiv : ∀ (N : ℕ) (y : ℝ),
      HasDerivAt (fun z => ∑ n ∈ Finset.range N, c n * z ^ n)
        (∑ n ∈ Finset.range N, (n : ℝ) * c n * y ^ (n - 1)) y := by
    intro N y
    have hsum : HasDerivAt (∑ n ∈ Finset.range N, fun z : ℝ => c n * z ^ n)
        (∑ n ∈ Finset.range N, (n : ℝ) * c n * y ^ (n - 1)) y := by
      refine HasDerivAt.sum (fun n _ => ?_)
      have h : HasDerivAt (fun z : ℝ => c n * z ^ n) (c n * ((n : ℝ) * y ^ (n - 1))) y :=
        (hasDerivAt_pow n y).const_mul (c n)
      have heq2 : c n * ((n : ℝ) * y ^ (n - 1)) = (n : ℝ) * c n * y ^ (n - 1) := by ring
      rwa [heq2] at h
    have heq : (∑ n ∈ Finset.range N, fun z : ℝ => c n * z ^ n)
        = fun z => ∑ n ∈ Finset.range N, c n * z ^ n := by
      funext z
      simp
    rwa [heq] at hsum
  refine hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo huni
    (Eventually.of_forall fun N y _ => hderiv N y) (fun y hy => ?_) ?_
  · rw [← htf y hy]
    exact (hsf y hy).hasSum.tendsto_sum_nat
  · exact Set.mem_Ioo.2 ⟨(abs_lt.1 hxr).1, (abs_lt.1 hxr).2⟩

end RudinLoc81

open Filter Topology Rudin in
theorem solution (c : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hconv : ∀ x : ℝ, |x| < R → SeriesConverges (fun n => c n * x ^ n))
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, |x| < R → SeriesConvergesTo (fun n => c n * x ^ n) (f x))
    (g : ℝ → ℝ) (hg : ∀ x : ℝ, |x| < R →
      SeriesConvergesTo (fun n => (n : ℝ) * c n * x ^ (n - 1)) (g x)) :
    ∀ x : ℝ, |x| < R → HasDerivAt f (g x) x :=
  RudinLoc81.rudin_8_1 c R hR hconv f hf g hg
