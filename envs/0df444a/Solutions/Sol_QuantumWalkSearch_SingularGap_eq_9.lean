-- Prove2me | solution 1 for QuantumWalkSearch.SingularGap.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T23:07:51.74898+00:00
-- url     : https://prove2.me/submissions/699b41e8-7a2c-4870-8ddf-954214f972f0

import Mathlib
import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant

open Matrix

open QuantumWalkSearch.SingularGap in
theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π)
    (u v : EuclideanSpace ℂ X) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    inner ℂ u (discriminantOp P π v) =
        ∑ x, ∑ y, star (u x) * v y * ((Real.sqrt (π x / π y) * P x y : ℝ) : ℂ) ∧
      ‖inner ℂ u (discriminantOp P π v)‖ ≤
        Real.sqrt (∑ x, ∑ y, ‖u x‖ ^ 2 * P x y) *
          Real.sqrt (∑ x, ∑ y, ‖v y‖ ^ 2 * (π x / π y) * P x y) ∧
      Real.sqrt (∑ x, ∑ y, ‖u x‖ ^ 2 * P x y) *
          Real.sqrt (∑ x, ∑ y, ‖v y‖ ^ 2 * (π x / π y) * P x y) ≤ 1 := by
  have hPnn : ∀ x y, 0 ≤ P x y := fun x y => nonneg_of_mem_rowStochastic hP
  have hπpos := hπ.pos
  have h1 : inner ℂ u (discriminantOp P π v) =
      ∑ x, ∑ y, star (u x) * v y * ((Real.sqrt (π x / π y) * P x y : ℝ) : ℂ) := by
    rw [discriminantOp, Matrix.toEuclideanLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, mulVec, WithLp.ofLp_toLp, Finset.sum_mul, Pi.star_apply]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    rw [discriminant, of_apply, Real.sqrt_div (hπpos x).le]
    push_cast
    ring
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]
    have hn : ‖∑ x, ∑ y, star (u x) * v y * ((Real.sqrt (π x / π y) * P x y : ℝ) : ℂ)‖ ≤
        ∑ x, ∑ y, (‖u x‖ * Real.sqrt (P x y)) *
          (‖v y‖ * Real.sqrt (π x / π y) * Real.sqrt (P x y)) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _ => ?_))
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun y _ => ?_)))
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hPnn x y))]
      have : Real.sqrt (P x y) * Real.sqrt (P x y) = P x y := Real.mul_self_sqrt (hPnn x y)
      calc ‖u x‖ * ‖v y‖ * (Real.sqrt (π x / π y) * P x y)
          = ‖u x‖ * ‖v y‖ * (Real.sqrt (π x / π y) * (Real.sqrt (P x y) * Real.sqrt (P x y))) := by
            rw [this]
        _ = _ := by ring
    refine hn.trans ?_
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (X × X))
      (fun p => ‖u p.1‖ * Real.sqrt (P p.1 p.2))
      (fun p => ‖v p.2‖ * Real.sqrt (π p.1 / π p.2) * Real.sqrt (P p.1 p.2))
    simp only [← Finset.univ_product_univ, Finset.sum_product] at hcs
    have e1 : ∀ x y, (‖u x‖ * Real.sqrt (P x y)) ^ 2 = ‖u x‖ ^ 2 * P x y := by
      intro x y; rw [mul_pow, Real.sq_sqrt (hPnn x y)]
    have e2 : ∀ x y, (‖v y‖ * Real.sqrt (π x / π y) * Real.sqrt (P x y)) ^ 2 =
        ‖v y‖ ^ 2 * (π x / π y) * P x y := by
      intro x y
      rw [mul_pow, mul_pow, Real.sq_sqrt (hPnn x y),
        Real.sq_sqrt (div_nonneg (hπpos x).le (hπpos y).le)]
    simp only [e1, e2] at hcs
    exact hcs
  · have hu2 : ∑ x, ‖u x‖ ^ 2 = 1 := by
      rw [← EuclideanSpace.norm_sq_eq, hu, one_pow]
    have hv2 : ∑ y, ‖v y‖ ^ 2 = 1 := by
      rw [← EuclideanSpace.norm_sq_eq, hv, one_pow]
    have s1 : ∑ x, ∑ y, ‖u x‖ ^ 2 * P x y = 1 := by
      rw [← hu2]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.mul_sum, sum_row_of_mem_rowStochastic hP x, mul_one]
    have s2 : ∑ x, ∑ y, ‖v y‖ ^ 2 * (π x / π y) * P x y = 1 := by
      rw [Finset.sum_comm, ← hv2]
      apply Finset.sum_congr rfl; intro y _
      have : ∑ x, ‖v y‖ ^ 2 * (π x / π y) * P x y = ‖v y‖ ^ 2 / π y * ∑ x, π x * P x y := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
      rw [this, hπ.stationary y]
      field_simp [(hπpos y).ne']
    rw [s1, s2, Real.sqrt_one, one_mul]
