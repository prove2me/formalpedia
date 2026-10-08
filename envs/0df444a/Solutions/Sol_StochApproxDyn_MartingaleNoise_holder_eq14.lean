-- Prove2me | solution 1 for StochApproxDyn.MartingaleNoise.holder_eq14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:34:03.188288+00:00
-- url     : https://prove2.me/submissions/89195805-8177-42bc-be6e-809d772be6fb

import Mathlib

set_option autoImplicit false

open Finset in
theorem solution {ι : Type*} (s : Finset ι) (α β : ι → ℝ) (hα : ∀ i ∈ s, 0 ≤ α i)
    (u δ : ℝ) (hu : 1 < u) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∑ i ∈ s, |α i * β i|) ^ u ≤
      (∑ i ∈ s, α i ^ (δ * u / (u - 1))) ^ (u - 1) *
        ∑ i ∈ s, α i ^ ((1 - δ) * u) * |β i| ^ u := by
  have hu1 : 0 < u - 1 := by linarith
  have hu0 : 0 < u := by linarith
  have hpq : (u / (u - 1)).HolderConjugate u := (Real.HolderConjugate.conjExponent hu).symm
  have key := Real.inner_le_Lp_mul_Lq_of_nonneg s (f := fun i => α i ^ δ)
    (g := fun i => α i ^ (1 - δ) * |β i|) hpq
    (fun i hi => Real.rpow_nonneg (hα i hi) _)
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hα i hi) _) (abs_nonneg _))
  have hL : ∑ i ∈ s, |α i * β i| = ∑ i ∈ s, α i ^ δ * (α i ^ (1 - δ) * |β i|) := by
    refine sum_congr rfl fun i hi => ?_
    rw [← mul_assoc, ← Real.rpow_add' (hα i hi) (by norm_num), add_sub_cancel, Real.rpow_one,
      abs_mul, abs_of_nonneg (hα i hi)]
  have hA : ∑ i ∈ s, (α i ^ δ) ^ (u / (u - 1)) = ∑ i ∈ s, α i ^ (δ * u / (u - 1)) := by
    refine sum_congr rfl fun i hi => ?_
    rw [← Real.rpow_mul (hα i hi), mul_div_assoc]
  have hB : ∑ i ∈ s, (α i ^ (1 - δ) * |β i|) ^ u = ∑ i ∈ s, α i ^ ((1 - δ) * u) * |β i| ^ u := by
    refine sum_congr rfl fun i hi => ?_
    rw [Real.mul_rpow (Real.rpow_nonneg (hα i hi) _) (abs_nonneg _), ← Real.rpow_mul (hα i hi)]
  rw [hA, hB, ← hL] at key
  have hA0 : 0 ≤ ∑ i ∈ s, α i ^ (δ * u / (u - 1)) :=
    sum_nonneg fun i hi => Real.rpow_nonneg (hα i hi) _
  have hB0 : 0 ≤ ∑ i ∈ s, α i ^ ((1 - δ) * u) * |β i| ^ u :=
    sum_nonneg fun i hi => mul_nonneg (Real.rpow_nonneg (hα i hi) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hS0 : 0 ≤ ∑ i ∈ s, |α i * β i| := sum_nonneg fun i _ => abs_nonneg _
  calc (∑ i ∈ s, |α i * β i|) ^ u
      ≤ ((∑ i ∈ s, α i ^ (δ * u / (u - 1))) ^ (1 / (u / (u - 1))) *
          (∑ i ∈ s, α i ^ ((1 - δ) * u) * |β i| ^ u) ^ (1 / u)) ^ u :=
        Real.rpow_le_rpow hS0 key hu0.le
    _ = (∑ i ∈ s, α i ^ (δ * u / (u - 1))) ^ (u - 1) *
          ∑ i ∈ s, α i ^ ((1 - δ) * u) * |β i| ^ u := by
        rw [Real.mul_rpow (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _),
          ← Real.rpow_mul hA0, ← Real.rpow_mul hB0]
        congr 2
        · field_simp
        · field_simp
          simp
