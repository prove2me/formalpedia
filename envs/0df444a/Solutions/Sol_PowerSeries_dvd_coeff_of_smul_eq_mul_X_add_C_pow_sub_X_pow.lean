-- Prove2me | solution 1 for PowerSeries.dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1e76e7eb-f7a2-5847-b2a8-266708a4d7c3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow

set_option autoImplicit false

p2m_open "IsLocalRing PowerSeries P2MW.S_PowerSeries_dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow.PowerSeries"

namespace PowerSeries
p2m_export "PowerSeries" "coeff_mul_X_pow' constantCoeff coeff_C_mul order C coeff X"
p2m_open "PowerSeries"

variable {A : Type*} [CommRing A]

theorem exists_X_add_C_pow_succ_eq_add_mul_sq (d : A) (N : ℕ) :
    ∃ R : A⟦X⟧, (X + C d) ^ (N + 1) =
      X ^ (N + 1) + C ((N + 1 : A) * d) * X ^ N + C (d ^ 2) * R := by
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨(X + C d) * R + C ((N + 1 : A)) * X ^ N, ?_⟩
    rw [pow_succ, hR]
    simp only [map_mul, map_pow, map_add, map_one, map_natCast, Nat.cast_add, Nat.cast_one]
    ring

theorem exists_coeff_eq_of_smul_eq_mul_X_add_C_pow_sub_X_pow {N : ℕ} {d e : A} {u F : A⟦X⟧}
    (hF : e • F = u * (X + C d) ^ (N + 1) - X ^ (N + 1)) :
    ∃ R : A⟦X⟧,
      (∀ j, j + 1 ≤ N → e * coeff j F = d ^ 2 * coeff j (u * R)) ∧
      e * coeff N F = d * ((N + 1 : A) * constantCoeff u + d * coeff N (u * R)) ∧
      e * coeff (N + 1) F =
        (constantCoeff u - 1) + d * ((N + 1 : A) * coeff 1 u + d * coeff (N + 1) (u * R)) := by
  obtain ⟨R, hR⟩ := exists_X_add_C_pow_succ_eq_add_mul_sq d N
  have hP : u * (X + C d) ^ (N + 1) - X ^ (N + 1) =
      (u - 1) * X ^ (N + 1) + C ((N + 1 : A) * d) * (u * X ^ N) + C (d ^ 2) * (u * R) := by
    rw [hR]; ring
  have hc : ∀ i, e * coeff i F = coeff i ((u - 1) * X ^ (N + 1)) +
      (N + 1 : A) * d * coeff i (u * X ^ N) + d ^ 2 * coeff i (u * R) := by
    intro i
    have h := congr_arg (coeff i) hF
    rw [hP] at h
    simpa only [map_smul, smul_eq_mul, map_add, coeff_C_mul] using h
  refine ⟨R, ?_, ?_, ?_⟩
  · intro j hj
    have h1 : ¬ (N + 1 ≤ j) := by omega
    have h2 : ¬ (N ≤ j) := by omega
    rw [hc j]
    simp [coeff_mul_X_pow', h1, h2]
  · rw [hc N]
    simp [coeff_mul_X_pow']
    ring
  · rw [hc (N + 1)]
    simp [coeff_mul_X_pow']
    ring

end PowerSeries

theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    {n : ℕ} (hn : IsUnit (n : A)) {d e : A} (hd : d ∈ maximalIdeal A) (he : e ≠ 0)
    {u F : A⟦X⟧} (hF : e • F = u * (X + C d) ^ n - X ^ n) {j : ℕ} (hj : j + 2 ≤ n) :
    d ∣ coeff j F := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  obtain ⟨R, hlow, hN, hN1⟩ := exists_coeff_eq_of_smul_eq_mul_X_add_C_pow_sub_X_pow hF
  have ej : e * coeff j F = d ^ 2 * coeff j (u * R) := hlow j (by omega)
  by_cases hu : IsUnit (constantCoeff u)
  ·
    have hv : IsUnit ((N + 1 : A) * constantCoeff u + d * coeff N (u * R)) := by
      have h1 : IsUnit ((N + 1 : A) * constantCoeff u) := by
        have : IsUnit ((N + 1 : ℕ) : A) := hn
        exact_mod_cast this.mul hu
      by_contra h
      have hmem : (N + 1 : A) * constantCoeff u + d * coeff N (u * R) ∈ maximalIdeal A := h
      have h2 : (N + 1 : A) * constantCoeff u ∈ maximalIdeal A := by
        simpa using sub_mem hmem (Ideal.mul_mem_right (coeff N (u * R)) _ hd)
      exact h2 h1
    obtain ⟨v, hv'⟩ := hv
    rw [← hv'] at hN

    have hdw : d = e * (coeff N F * ↑v⁻¹) := by
      calc d = d * ↑v * ↑v⁻¹ := by simp
        _ = e * coeff N F * ↑v⁻¹ := by rw [hN]
        _ = e * (coeff N F * ↑v⁻¹) := by ring
    refine ⟨coeff N F * ↑v⁻¹ * coeff j (u * R), mul_left_cancel₀ he ?_⟩
    rw [ej]
    calc d ^ 2 * coeff j (u * R) = d * d * coeff j (u * R) := by ring
      _ = d * (e * (coeff N F * ↑v⁻¹)) * coeff j (u * R) := by rw [← hdw]
      _ = e * (d * (coeff N F * ↑v⁻¹ * coeff j (u * R))) := by ring
  ·
    have hm : constantCoeff u + d * ((N + 1 : A) * coeff 1 u + d * coeff (N + 1) (u * R)) ∈
        maximalIdeal A :=
      add_mem hu (Ideal.mul_mem_right _ _ hd)
    have hunit : IsUnit (e * coeff (N + 1) F) := by
      rw [hN1]
      have : constantCoeff u - 1 + d * ((N + 1 : A) * coeff 1 u + d * coeff (N + 1) (u * R)) =
          -(1 - (constantCoeff u + d * ((N + 1 : A) * coeff 1 u + d * coeff (N + 1) (u * R)))) := by
        ring
      rw [this]
      exact (isUnit_one_sub_self_of_mem_nonunits _ hm).neg
    obtain ⟨eu, heu⟩ := isUnit_of_mul_isUnit_left hunit
    refine ⟨↑eu⁻¹ * d * coeff j (u * R), ?_⟩
    calc coeff j F = ↑eu⁻¹ * (↑eu * coeff j F) := (Units.inv_mul_cancel_left _ _).symm
      _ = ↑eu⁻¹ * (d ^ 2 * coeff j (u * R)) := by rw [heu, ej]
      _ = d * (↑eu⁻¹ * d * coeff j (u * R)) := by ring

end S_PowerSeries_dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow
end P2MW
export P2MW.S_PowerSeries_dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow (solution)
