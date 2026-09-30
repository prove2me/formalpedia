-- Prove2me | solution 1 for WeierstrassEllipticZeta.nilpotent_shift_geometric_inverse
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T22:15:04.726832+00:00
-- url     : https://prove2.me/submissions/307c70a9-bf70-4ad1-a4ad-1d7e7dd0e30b

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Ring



theorem solution
    (K A : Type*) [Field K] [CommRing A] (φ : K →+* A)
    (x : A) (N : ℕ) (hx : x ^ N = 0) (c : K) (hc : c ≠ 0) :
    let b := φ c⁻¹ * ∑ i ∈ Finset.range N, (-(φ c⁻¹ * x)) ^ i
    (x + φ c) * b = 1 ∧ b * (x + φ c) = 1 ∧ IsUnit (x + φ c) := by
  classical
  let t := -(φ c⁻¹ * x)
  have ht : t ^ N = 0 := by
    dsimp [t]
    rw [neg_pow, mul_pow, hx, mul_zero, mul_zero]
  have hc' : φ c * φ c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have hfactor : (x + φ c) * φ c⁻¹ = 1 - t := by
    rw [add_mul, hc']
    dsimp [t]
    ring
  have hleft : (x + φ c) * (φ c⁻¹ * ∑ i ∈ Finset.range N, t ^ i) = 1 := by
    rw [← mul_assoc, hfactor, mul_neg_geom_sum, ht, sub_zero]
  refine ⟨hleft, ?_, ?_⟩
  · rwa [mul_comm]
  · exact IsUnit.of_mul_eq_one _ hleft

