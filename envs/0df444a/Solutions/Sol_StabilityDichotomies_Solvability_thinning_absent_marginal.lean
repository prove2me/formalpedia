-- Prove2me | solution 1 for StabilityDichotomies.Solvability.thinning_absent_marginal
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:40:01.821204+00:00
-- url     : https://prove2.me/submissions/0d78b69f-adff-410f-a989-13b662ca5ac1

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability

private theorem bernoulli_absent_marginal (m : ℕ) (i : Fin m) (p : ℝ) :
    (∑ mask : Fin m → Bool, retentionWeight p mask * (if mask i then 0 else 1)) = 1 - p := by
  let f : Fin m → Bool → ℝ := fun j b =>
    (if b then p else 1 - p) * (if j = i then (if b then 0 else 1) else 1)
  have hprod (mask : Fin m → Bool) :
      retentionWeight p mask * (if mask i then 0 else 1) = ∏ j, f j (mask j) := by
    unfold retentionWeight f
    rw [Finset.prod_mul_distrib]
    congr 1
    symm
    rw [Finset.prod_eq_single i]
    · simp
    · intro j hj hji; simp [hji]
    · simp
  simp_rw [hprod, ← Fintype.prod_sum]
  have hf (j : Fin m) : (∑ b : Bool, f j b) = if j = i then 1 - p else 1 := by
    by_cases h : j = i <;> simp [f, h, Fintype.sum_bool]
  simp_rw [hf]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji; simp [hji]
  · simp

theorem solution (m : ℕ) (i : Fin m) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε⁻¹ * ∫ p in (1 - ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask * (if mask i then 0 else 1) = ε / 2 := by
  simp_rw [bernoulli_absent_marginal]
  have hi : (∫ p : ℝ in (1 - ε)..1, 1 - p) =
      (∫ _p : ℝ in (1 - ε)..1, (1 : ℝ)) - (∫ p : ℝ in (1 - ε)..1, p) := by
    exact intervalIntegral.integral_sub intervalIntegrable_const (continuous_id.intervalIntegrable _ _)
  rw [hi]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_sub_cancel,
    integral_id]
  have hne : ε ≠ 0 := ne_of_gt hε
  field_simp
  ring
