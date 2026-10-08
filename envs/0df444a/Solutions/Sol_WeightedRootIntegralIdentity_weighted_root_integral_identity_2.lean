-- Prove2me | solution 2 for WeightedRootIntegralIdentity.weighted_root_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-14T14:01:37.985893+00:00
-- url     : https://prove2.me/submissions/f14a2f13-a8bf-4196-aeb3-c012d0682b00

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_geometric_mean_integral_identity
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1)) :
    (∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
      = ((1 : ℝ) / n) * (∑ i ∈ Finset.range n, a i)
          - Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹) := by
  have hnNat : 0 < n := lt_of_lt_of_le (by omega : 0 < 2) hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hwpos : ∀ i < n, 0 < ((n : ℝ)⁻¹) := by
    intro i hi
    positivity
  have hwsum : (∑ i ∈ Finset.range n, ((n : ℝ)⁻¹)) = 1 := by
    simp [hnReal.ne']
  have h :=
    WeightedRootIntegralIdentity.weighted_geometric_mean_integral_identity
      n hn a (fun _ => ((n : ℝ)⁻¹)) hpos hmono hwpos hwsum
  have hprod :
      (∏ i ∈ Finset.range n, Real.rpow (a i) ((n : ℝ)⁻¹)) =
        Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹) := by
    apply Real.finsetProd_rpow
    intro i hi
    exact (hpos i (Finset.mem_range.mp hi)).le
  rw [hprod] at h
  simpa [div_eq_mul_inv, Finset.mul_sum] using h
