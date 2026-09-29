-- Prove2me | solution 1 for ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/50ea2e9e-cd53-51a5-9390-67197424e14c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    (q₁ : Polynomial L) (hq₁ : q₁ ≠ 0) :
    ∃ q : Polynomial A, ∃ c : L, c ≠ 0 ∧
      (q.map A.subtype = Polynomial.C c⁻¹ * q₁) ∧ q.map (IsLocalRing.residue A) ≠ 0 := by
  classical

  have hne : q₁.support.Nonempty := Polynomial.support_nonempty.mpr hq₁
  obtain ⟨i₀, hi₀s, hi₀max⟩ :=
    q₁.support.exists_max_image (fun i => A.valuation (q₁.coeff i)) hne
  set c := q₁.coeff i₀ with hc
  have hc0 : c ≠ 0 := Polynomial.mem_support_iff.mp hi₀s

  have hmem : ∀ i, c⁻¹ * q₁.coeff i ∈ A := by
    intro i
    rcases eq_or_ne (q₁.coeff i) 0 with h0 | h0
    · rw [h0, mul_zero]; exact A.zero_mem
    rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    have hi : i ∈ q₁.support := Polynomial.mem_support_iff.mpr h0
    have hle := hi₀max i hi
    have hvc : A.valuation c ≠ 0 := by simpa using hc0
    calc (A.valuation c)⁻¹ * A.valuation (q₁.coeff i)
        ≤ (A.valuation c)⁻¹ * A.valuation c := mul_le_mul_right hle _
      _ = 1 := inv_mul_cancel₀ hvc

  have hcoeffs : ↑(C c⁻¹ * q₁).coeffs ⊆ (A.toSubring : Set L) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    rw [coeff_C_mul]
    exact hmem i
  set q : Polynomial A := (C c⁻¹ * q₁).toSubring A.toSubring hcoeffs with hq
  refine ⟨q, c, hc0, ?_, ?_⟩
  ·
    rw [hq]
    exact Polynomial.map_toSubring _ _ hcoeffs
  ·
    have hqmap : q.map A.subtype = C c⁻¹ * q₁ := by
      rw [hq]; exact Polynomial.map_toSubring _ _ hcoeffs
    have hone : q.coeff i₀ = 1 := by
      apply Subtype.ext
      have h2 : A.subtype (q.coeff i₀) = (C c⁻¹ * q₁).coeff i₀ := by
        rw [← Polynomial.coeff_map, hqmap]
      rw [ValuationSubring.subtype_apply] at h2
      rw [show ((1 : A) : L) = 1 from rfl, h2, coeff_C_mul, ← hc, inv_mul_cancel₀ hc0]
    intro hzero
    have h1 : (q.map (IsLocalRing.residue A)).coeff i₀ = 0 := by rw [hzero]; simp
    rw [coeff_map, hone, map_one] at h1
    exact one_ne_zero h1

end S_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero
end P2MW
export P2MW.S_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero (solution)
