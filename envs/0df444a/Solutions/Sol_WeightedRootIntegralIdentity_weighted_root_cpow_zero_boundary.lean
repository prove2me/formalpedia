-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_cpow_zero_boundary
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-14T14:15:21.516715+00:00
-- url     : https://prove2.me/submissions/352c4810-3af3-4703-a3ca-530685b7227b

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_finset_boundary_product
open scoped BigOperators

theorem solution
    (n : ℕ) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    (∏ i ∈ Finset.range n,
        (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))) =
      -((∏ i ∈ Finset.range n, Real.rpow (a i) (w i) : ℝ) : ℂ) := by
  have hzero_ne : ∀ i ∈ Finset.range n, -a i ≠ 0 := by
    intro i hi
    exact neg_ne_zero.mpr (ne_of_gt (hpos i (Finset.mem_range.mp hi)))
  have hfilter :
      (Finset.range n).filter (fun i => -a i < 0) = Finset.range n := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact neg_neg_of_pos (hpos i (Finset.mem_range.mp hi))
  have habsprod :
      (∏ i ∈ Finset.range n, Real.rpow |-a i| (w i)) =
        ∏ i ∈ Finset.range n, Real.rpow (a i) (w i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [abs_neg, abs_of_pos (hpos i (Finset.mem_range.mp hi))]
  have hb :=
    WeightedRootIntegralIdentity.cpow_finset_boundary_product
      (Finset.range n) (fun i => -a i) w hzero_ne
  rw [hfilter, hwsum, habsprod] at hb
  simpa [Complex.exp_pi_mul_I] using hb
