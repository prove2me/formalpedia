-- Prove2me | solution 1 for ValuationSubring.aeval_mem_and_inv_mem_of_forall_mem_iff_of_mul_single_eq_ofPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b4e6fb4a-6c26-59f6-92e1-1a67131b66fa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_aeval_mem_and_inv_mem_of_forall_mem_iff_of_mul_single_eq_ofPowerSeries

set_option autoImplicit false

open Polynomial in

theorem solution
    {L : Type*} [Field L] (K : IntermediateField L (LaurentSeries L))
    {A : Type*} [CommRing A] [Algebra A ↥K] (φ : A →+* L) (hinj : Function.Injective φ)
    (hφ : ∀ a : A, ((algebraMap A ↥K a : ↥K) : LaurentSeries L) = HahnSeries.C (φ a))
    {κ : Type*} [CommRing κ] [Nontrivial κ] (res : A →+* κ)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ g : ↥K, g ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map res ≠ 0 ∧
      (g : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map φ) = HahnSeries.ofPowerSeries ℤ L (x.map φ))
    (f : ↥K) (z : PowerSeries A) (m : ℕ) (hm : 0 < m)
    (hz : (f : LaurentSeries L) * HahnSeries.single (m : ℤ) 1 = HahnSeries.ofPowerSeries ℤ L (z.map φ))
    (hz1 : PowerSeries.coeff 0 z = 1)
    (Q : Polynomial A) (hQ : Q.map res ≠ 0) :
    Polynomial.aeval f Q ∈ W₀ ∧ (Polynomial.aeval f Q)⁻¹ ∈ W₀ := by
  classical
  set n := Q.natDegree with hn

  set Aps : PowerSeries A :=
    ∑ i ∈ Finset.range (n + 1), PowerSeries.C (Q.coeff i) * PowerSeries.X ^ (m * (n - i)) * z ^ i with hAps

  have hcoe : ((Polynomial.aeval f Q : ↥K) : LaurentSeries L) =
      ∑ i ∈ Finset.range (n + 1), HahnSeries.C (φ (Q.coeff i)) * (f : LaurentSeries L) ^ i := by
    rw [Polynomial.aeval_eq_sum_range, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, MulMemClass.coe_mul, SubmonoidClass.coe_pow, hφ]
  have hsum : ((Polynomial.aeval f Q : ↥K) : LaurentSeries L) * HahnSeries.single ((m * n : ℕ) : ℤ) (1 : L) =
      HahnSeries.ofPowerSeries ℤ L (Aps.map φ) := by
    rw [hcoe, Finset.sum_mul, hAps, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsplit : HahnSeries.single ((m * n : ℕ) : ℤ) (1 : L) =
        HahnSeries.single ((m * (n - i) : ℕ) : ℤ) (1 : L) * (HahnSeries.single (m : ℤ) (1 : L)) ^ i := by
      rw [HahnSeries.single_pow, HahnSeries.single_mul_single, one_pow, mul_one]
      congr 1
      simp only [nsmul_eq_mul]
      push_cast
      rw [Nat.cast_sub hi']
      push_cast
      ring
    have e1 : HahnSeries.ofPowerSeries ℤ L ((PowerSeries.X ^ (m * (n - i)) : PowerSeries A).map φ) =
        HahnSeries.single ((m * (n - i) : ℕ) : ℤ) (1 : L) := by
      rw [map_pow, PowerSeries.map_X, HahnSeries.ofPowerSeries_X_pow]
    have e2 : HahnSeries.ofPowerSeries ℤ L ((z ^ i).map φ) = (HahnSeries.ofPowerSeries ℤ L (z.map φ)) ^ i := by
      rw [map_pow, map_pow]
    rw [hsplit, map_mul, map_mul, map_mul, map_mul, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, e1, e2, ← hz]
    ring

  have hAred : Aps.map res ≠ 0 := by
    set i₀ := (Q.map res).natDegree with hi₀
    have hi₀n : i₀ ≤ n := Polynomial.natDegree_map_le
    have hlead : res (Q.coeff i₀) ≠ 0 := by
      have := Polynomial.leadingCoeff_ne_zero.mpr hQ
      rwa [Polynomial.leadingCoeff, Polynomial.coeff_map] at this
    have hzc : PowerSeries.constantCoeff (z.map res) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, hz1, map_one]
    intro h0
    apply hlead
    have hc : PowerSeries.coeff (m * (n - i₀)) (Aps.map res) = res (Q.coeff i₀) := by
      rw [hAps, map_sum, map_sum, Finset.sum_eq_single i₀]
      · simp only [map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
        rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
          PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hzc, one_pow, mul_one]
      · intro i hi hne
        simp only [map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
        rw [mul_assoc, PowerSeries.coeff_C_mul]
        rcases lt_or_gt_of_ne hne with hlt | hgt
        ·
          rw [PowerSeries.coeff_X_pow_mul', if_neg, mul_zero]
          intro hle
          have h1 : n - i₀ < n - i := by omega
          have h2 : m * (n - i₀) < m * (n - i) := Nat.mul_lt_mul_of_pos_left h1 hm
          omega
        ·
          rw [show res (Q.coeff i) = (Q.map res).coeff i from (Polynomial.coeff_map _ _).symm,
            Polynomial.coeff_eq_zero_of_natDegree_lt hgt, zero_mul]
      · intro h
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi₀n)) h
    rw [← hc, h0, map_zero]

  have hXred : (PowerSeries.X ^ (m * n) : PowerSeries A).map res ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.coeff (m * n)) h
    simp only [map_pow, PowerSeries.map_X, PowerSeries.coeff_X_pow_self, map_zero] at this
    exact one_ne_zero this
  have hXφ : HahnSeries.ofPowerSeries ℤ L ((PowerSeries.X ^ (m * n) : PowerSeries A).map φ) =
      HahnSeries.single ((m * n : ℕ) : ℤ) (1 : L) := by
    rw [map_pow, PowerSeries.map_X, HahnSeries.ofPowerSeries_X_pow]
  have hmem : Polynomial.aeval f Q ∈ W₀ := (hW₀ _).mpr ⟨Aps, PowerSeries.X ^ (m * n), hXred, by rw [hXφ, hsum]⟩
  refine ⟨hmem, (hW₀ _).mpr ⟨PowerSeries.X ^ (m * n), Aps, hAred, ?_⟩⟩
  have hne : ((Polynomial.aeval f Q : ↥K) : LaurentSeries L) ≠ 0 := by
    intro h0
    have h1 : HahnSeries.ofPowerSeries ℤ L (Aps.map φ) = 0 := by rw [← hsum, h0, zero_mul]
    have h2 : Aps.map φ = 0 := HahnSeries.ofPowerSeries_injective (by rw [h1, map_zero])
    have h3 : Aps = 0 := PowerSeries.map_injective φ hinj (by rw [h2, map_zero])
    exact hAred (by rw [h3, map_zero])
  rw [hXφ, ← hsum, IntermediateField.coe_inv, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end S_ValuationSubring_aeval_mem_and_inv_mem_of_forall_mem_iff_of_mul_single_eq_ofPowerSeries
end P2MW
export P2MW.S_ValuationSubring_aeval_mem_and_inv_mem_of_forall_mem_iff_of_mul_single_eq_ofPowerSeries (solution)
