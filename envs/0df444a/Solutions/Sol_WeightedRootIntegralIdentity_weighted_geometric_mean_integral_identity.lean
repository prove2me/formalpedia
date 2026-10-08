-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_geometric_mean_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T18:57:24.96428+00:00
-- url     : https://prove2.me/submissions/0c935ecd-e4de-40a4-b35d-2e891cf6ca0c

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_complex_boundary_jump
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_geometric_mean_cauchy_boundary_integral

open scoped BigOperators Interval
open WeightedRootIntegralIdentity

theorem solution
    (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    (∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * (∑ i ∈ Finset.range (k + 1), w i)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((w i))) / x)
      = (∑ i ∈ Finset.range n, w i * a i)
          - (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) := by
  classical
  -- the integrand coming from the complex boundary values
  set G : ℝ → ℝ :=
    fun x => (∏ i ∈ Finset.range n, ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ))).im / x with hG
  -- the real integrand
  set F : ℝ → ℝ := fun x => (∏ i ∈ Finset.range n, Real.rpow |x - a i| (w i)) / x with hF
  have hapos : ∀ j, j ≤ n - 1 → 0 < a j := fun j hj => hpos j (by omega)
  -- F is continuous on each subinterval
  have hFcont : ∀ k, k < n - 1 → ContinuousOn F (Set.uIcc (a k) (a (k + 1))) := by
    intro k hk
    have hnum : Continuous fun x : ℝ => ∏ i ∈ Finset.range n, Real.rpow |x - a i| (w i) := by
      refine continuous_finsetProd _ ?_
      intro i hi
      have : Continuous fun x : ℝ => |x - a i| := (continuous_id.sub continuous_const).abs
      exact this.rpow_const fun x => Or.inr (le_of_lt (hwpos i (Finset.mem_range.mp hi)))
    refine ContinuousOn.div hnum.continuousOn continuousOn_id ?_
    intro x hx
    have hle : a k ≤ a (k + 1) := hmono k hk
    rw [Set.uIcc_of_le hle] at hx
    have : 0 < a k := hapos k (by omega)
    exact ne_of_gt (lt_of_lt_of_le this hx.1)
  have hFint : ∀ k, k < n - 1 → IntervalIntegrable F MeasureTheory.volume (a k) (a (k + 1)) :=
    fun k hk => (hFcont k hk).intervalIntegrable
  -- both integrands vanish at every node
  have hzeroF : ∀ j, j < n → ∀ x : ℝ, x = a j → F x = 0 := by
    intro j hj x hx
    have hz : (∏ i ∈ Finset.range n, Real.rpow |x - a i| (w i)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_range.mpr hj) ?_
      rw [hx]
      simp [Real.zero_rpow (ne_of_gt (hwpos j hj))]
    simp only [hF, hz, zero_div]
  have hzeroG : ∀ j, j < n → ∀ x : ℝ, x = a j → G x = 0 := by
    intro j hj x hx
    have hz : (∏ i ∈ Finset.range n, ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ))) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_range.mpr hj) ?_
      rw [hx]
      have h0 : ((a j : ℂ) - (a j : ℂ)) = 0 := by ring
      rw [h0, Complex.zero_cpow]
      exact_mod_cast (ne_of_gt (hwpos j hj))
    simp only [hG, hz]
    simp
  -- identification of G with a multiple of F on each subinterval
  have heq : ∀ k, k < n - 1 →
      Set.EqOn G (fun x => Real.sin (Real.pi * (∑ i ∈ Finset.range (k + 1), w i)) * F x)
        (Set.uIcc (a k) (a (k + 1))) := by
    intro k hk x hx
    have hle : a k ≤ a (k + 1) := hmono k hk
    rw [Set.uIcc_of_le hle] at hx
    rcases eq_or_lt_of_le hx.1 with h1 | h1
    · simp only [hzeroG k (by omega) x h1.symm, hzeroF k (by omega) x h1.symm, mul_zero]
    · rcases eq_or_lt_of_le hx.2 with h2 | h2
      · simp only [hzeroG (k + 1) (by omega) x h2, hzeroF (k + 1) (by omega) x h2, mul_zero]
      · simp only [hG, hF]
        rw [weighted_root_complex_boundary_jump n a w hmono hwsum k hk x h1 h2]
        ring
  -- G is interval integrable on each subinterval
  have hGint : ∀ k, k < n - 1 → IntervalIntegrable G MeasureTheory.volume (a k) (a (k + 1)) := by
    intro k hk
    exact ((hFint k hk).const_mul _).congr (((heq k hk).symm).mono Set.uIoc_subset_uIcc)
  -- the pieces add up
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := G)
    (μ := MeasureTheory.volume) (a := a) (n := n - 1) (fun k hk => hGint k hk)
  have hpieces : ∀ k, k < n - 1 →
      (∫ x in a k..a (k + 1), G x)
        = Real.sin (Real.pi * (∑ i ∈ Finset.range (k + 1), w i)) *
            ∫ x in a k..a (k + 1), F x := by
    intro k hk
    rw [intervalIntegral.integral_congr (heq k hk), intervalIntegral.integral_const_mul]
  have hcauchy := weighted_geometric_mean_cauchy_boundary_integral n hn a w hpos hmono hwpos hwsum
  calc
    (∑ k ∈ Finset.range (n - 1),
        (Real.sin (Real.pi * (∑ i ∈ Finset.range (k + 1), w i)) / Real.pi) *
          ∫ x in a k..a (k + 1), F x)
        = (∑ k ∈ Finset.range (n - 1), ∫ x in a k..a (k + 1), G x) / Real.pi := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hpieces k (Finset.mem_range.mp hk)]
          ring
    _ = (∫ x in a 0..a (n - 1), G x) / Real.pi := by rw [hsum]
    _ = (∑ i ∈ Finset.range n, w i * a i)
          - (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) := hcauchy
