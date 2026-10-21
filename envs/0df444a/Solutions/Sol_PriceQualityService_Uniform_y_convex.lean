-- Prove2me | solution 1 for PriceQualityService.Uniform.y_convex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:26:00.726865+00:00
-- url     : https://prove2.me/submissions/ac599922-b2dc-4ccb-8cda-93ed9e3df616

import Mathlib
import Definitions.Def_PriceQualityService_Uniform_Reduction

set_option autoImplicit false
open PriceQualityService.Uniform

theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    ConvexOn ℝ Set.univ (yTotal α a b c s) := by
  have hexp : ∀ i, ConvexOn ℝ Set.univ (fun t => Real.exp (exponent α a b c s t i)) := by
    intro i
    have hqc : ConvexOn ℝ Set.univ (fun t : ℝ => exponent α a b c s t i) := by
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ p q hp hq hpq
      have hci : 0 < 4 * c i := by linarith [hc i]
      have hq1 : q = 1 - p := by linarith
      have key : 0 ≤ b i ^ 2 / (4 * c i) * (p * x ^ 2 + q * y ^ 2 - (p * x + q * y) ^ 2) := by
        apply mul_nonneg (div_nonneg (sq_nonneg _) hci.le)
        have : p * x ^ 2 + q * y ^ 2 - (p * x + q * y) ^ 2 = p * q * (x - y) ^ 2 := by
          rw [hq1]; ring
        rw [this]; positivity
      simp only [exponent, smul_eq_mul]
      have e1 : b i ^ 2 * (p * x + q * y) ^ 2 / (4 * c i) =
          b i ^ 2 / (4 * c i) * (p * x + q * y) ^ 2 := by ring
      have e2 : b i ^ 2 * x ^ 2 / (4 * c i) = b i ^ 2 / (4 * c i) * x ^ 2 := by ring
      have e3 : b i ^ 2 * y ^ 2 / (4 * c i) = b i ^ 2 / (4 * c i) * y ^ 2 := by ring
      rw [e1, e2, e3]
      have : α i ^ 2 / (4 * c i) = p * (α i ^ 2 / (4 * c i)) + q * (α i ^ 2 / (4 * c i)) := by
        rw [← add_mul, hpq, one_mul]
      nlinarith [key, this]
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ p q hp hq' hpq
    have h1 := hqc.2 (Set.mem_univ x) (Set.mem_univ y) hp hq' hpq
    have h2 := convexOn_exp.2 (Set.mem_univ (exponent α a b c s x i))
      (Set.mem_univ (exponent α a b c s y i)) hp hq' hpq
    simp only [smul_eq_mul] at h1 h2 ⊢
    exact (Real.exp_le_exp.mpr h1).trans h2
  have hsum : ∀ S : Finset (Fin N),
      ConvexOn ℝ Set.univ (fun t => ∑ i ∈ S, Real.exp (exponent α a b c s t i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using convexOn_const (0 : ℝ) convex_univ
    | insert i S hi ih =>
      simp_rw [Finset.sum_insert hi]
      exact (hexp i).add ih
  exact hsum Finset.univ
