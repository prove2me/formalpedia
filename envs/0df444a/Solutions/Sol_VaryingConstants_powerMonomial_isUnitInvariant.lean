-- Prove2me | solution 1 for VaryingConstants.powerMonomial_isUnitInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:04:03.124138+00:00
-- url     : https://prove2.me/submissions/8e4b98c6-de42-4d05-be0a-9545a5455e99

import Mathlib
import Definitions.Def_VaryingConstants_units

set_option autoImplicit false

open VaryingConstants in
theorem solution {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (a : Fin n → ℝ) (ha : a ∈ dimensionlessExponents D) :
    IsUnitInvariant D (powerMonomial a) := by
  intro x hx s hs
  have hker : Matrix.vecMul a D = 0 := by
    simpa [dimensionlessExponents, LinearMap.mem_ker] using ha
  have hcol : ∀ j, ∑ i, a i * D i j = 0 := by
    intro j
    have := congrFun hker j
    simpa [Matrix.vecMul, dotProduct] using this
  have hP : ∀ i, 0 ≤ ∏ j, s j ^ D i j := fun i =>
    Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hs j).le _
  have step1 : ∀ i, (x i * ∏ j, s j ^ D i j) ^ a i
      = x i ^ a i * ∏ j, s j ^ (a i * D i j) := by
    intro i
    rw [Real.mul_rpow (hx i).le (hP i),
      ← Real.finset_prod_rpow _ _ (fun j _ => Real.rpow_nonneg (hs j).le _)]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Real.rpow_mul (hs j).le, mul_comm]
  have step2 : ∏ i, ∏ j, s j ^ (a i * D i j) = 1 := by
    rw [Finset.prod_comm]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [← Real.rpow_sum_of_pos (hs j), hcol j, Real.rpow_zero]
  unfold powerMonomial unitRescale
  simp only [step1, Finset.prod_mul_distrib, step2, mul_one]
