-- Prove2me | solution 1 for PoissonDepTrials.SecondOrder.jensen_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T18:06:19.061482+00:00
-- url     : https://prove2.me/submissions/69f01b8e-7912-43cb-a114-1869e05f2c51

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Finset

open MeasureTheory ProbabilityTheory Finset in
theorem solution (n : ℕ) (p : ℕ → ℝ) (hp : ∀ i ∈ Finset.Icc 1 n, 0 ≤ p i)
    (hlam : 0 < ∑ i ∈ Finset.Icc 1 n, p i)
    (hpbar : ∀ i ∈ Finset.Icc 1 n, p i ≤ (∑ k ∈ Finset.Icc 1 n, p k) / 2) :
    (∑ k ∈ Finset.Icc 1 n, p k)⁻¹ * ∑ i ∈ Finset.Icc 1 n, p i ^ 2 *
        ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
          p j ^ 2 / ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i), p k ≤
      Real.sqrt 2 * (∑ k ∈ Finset.Icc 1 n, p k)⁻¹ * ∑ i ∈ Finset.Icc 1 n, p i ^ 3 := by
  set s := Finset.Icc 1 n with hs
  set S := ∑ k ∈ s, p k with hS
  set T := ∑ i ∈ s, p i ^ 3 with hT
  set Q := ∑ i ∈ s, p i ^ 2 with hQ
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i hi => pow_nonneg (hp i hi) 3
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i hi => sq_nonneg (p i)
  -- Cauchy–Schwarz on any subset of s
  have hCS : ∀ t ⊆ s, (∑ j ∈ t, p j ^ 2) ^ 2 ≤ (∑ j ∈ t, p j) * ∑ j ∈ t, p j ^ 3 := by
    intro t ht
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul t (fun j hj => hp j (ht hj))
      (fun j hj => pow_nonneg (hp j (ht hj)) 3) (fun j hj => le_of_eq (by ring))
  set c := Real.sqrt (2 * T / S) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  -- inner bound
  have hinner : ∀ i ∈ s, (∑ j ∈ s.filter (fun j : ℕ => j ≠ i),
        p j ^ 2 / ∑ k ∈ s.filter (fun k : ℕ => k ≠ i), p k) ≤ c := by
    intro i hi
    set F := s.filter (fun j : ℕ => j ≠ i) with hF
    have hFs : F ⊆ s := Finset.filter_subset _ _
    have hb : ∑ k ∈ F, p k = S - p i := by
      rw [hF, Finset.filter_ne', Finset.sum_erase_eq_sub hi]
    set b := ∑ k ∈ F, p k with hbdef
    have hbS : S ≤ 2 * b := by rw [hb]; linarith [hpbar i hi]
    have hbpos : 0 < b := by linarith
    set A := ∑ j ∈ F, p j ^ 2 with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => sq_nonneg (p j)
    have hTF : ∑ j ∈ F, p j ^ 3 ≤ T :=
      Finset.sum_le_sum_of_subset_of_nonneg hFs fun j hj _ => pow_nonneg (hp j hj) 3
    have hA2 : A ^ 2 ≤ b * T := by
      calc A ^ 2 ≤ b * ∑ j ∈ F, p j ^ 3 := hCS F hFs
        _ ≤ b * T := mul_le_mul_of_nonneg_left hTF hbpos.le
    rw [← Finset.sum_div]
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_div_iff₀ (by positivity) hlam]
    have h1 : A ^ 2 * S ≤ b * T * S := mul_le_mul_of_nonneg_right hA2 hlam.le
    have h2 : b * T * S ≤ b * T * (2 * b) :=
      mul_le_mul_of_nonneg_left hbS (mul_nonneg hbpos.le hT0)
    nlinarith
  have hsum : ∑ i ∈ s, p i ^ 2 * ∑ j ∈ s.filter (fun j : ℕ => j ≠ i),
        p j ^ 2 / ∑ k ∈ s.filter (fun k : ℕ => k ≠ i), p k ≤ Q * c := by
    rw [hQ, Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hinner i hi) (sq_nonneg (p i))
  have hQ2 : Q ^ 2 ≤ S * T := hCS s le_rfl
  have hQc : Q * c ≤ Real.sqrt 2 * T := by
    have e1 : Q * c = Real.sqrt (Q ^ 2 * (2 * T / S)) := by
      rw [Real.sqrt_mul (sq_nonneg Q), Real.sqrt_sq hQ0]
    have e2 : Real.sqrt 2 * T = Real.sqrt (2 * T ^ 2) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hT0]
    rw [e1, e2]
    apply Real.sqrt_le_sqrt
    rw [mul_div_assoc', div_le_iff₀ hlam]
    nlinarith
  have hSinv : 0 ≤ S⁻¹ := inv_nonneg.mpr hlam.le
  calc S⁻¹ * ∑ i ∈ s, p i ^ 2 * ∑ j ∈ s.filter (fun j : ℕ => j ≠ i),
        p j ^ 2 / ∑ k ∈ s.filter (fun k : ℕ => k ≠ i), p k
      ≤ S⁻¹ * (Q * c) := mul_le_mul_of_nonneg_left hsum hSinv
    _ ≤ S⁻¹ * (Real.sqrt 2 * T) := mul_le_mul_of_nonneg_left hQc hSinv
    _ = Real.sqrt 2 * S⁻¹ * T := by ring
