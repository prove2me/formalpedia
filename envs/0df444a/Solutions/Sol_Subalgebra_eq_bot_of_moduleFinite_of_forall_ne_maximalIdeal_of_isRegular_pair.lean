-- Prove2me | solution 1 for Subalgebra.eq_bot_of_moduleFinite_of_forall_ne_maximalIdeal_of_isRegular_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/07769b38-d054-55ac-8808-233e7811f8ee

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_eq_bot_of_moduleFinite_of_forall_ne_maximalIdeal_of_isRegular_pair

set_option autoImplicit false
set_option maxHeartbeats 800000

open IsLocalRing in
theorem solution
    {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (R : Subalgebra B (Localization (nonZeroDivisors B))) [Module.Finite B ↥R]
    (ha : ∀ (𝔮 : Ideal B) [𝔮.IsPrime], 𝔮 ≠ IsLocalRing.maximalIdeal B →
      ∀ r ∈ R, ∃ s : B, s ∉ 𝔮 ∧ (algebraMap B (Localization (nonZeroDivisors B)) s) * r ∈
        (algebraMap B (Localization (nonZeroDivisors B))).range)
    (hb : ∃ a b : B, a ∈ IsLocalRing.maximalIdeal B ∧ b ∈ IsLocalRing.maximalIdeal B ∧
      RingTheory.Sequence.IsRegular B [a, b]) :
    R = ⊥ := by
  classical
  obtain ⟨a, b, ha𝔪, hb𝔪, hreg⟩ := hb
  have hw := hreg.toIsWeaklyRegular
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hw
  obtain ⟨hrega, hw2⟩ := hw
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hw2
  obtain ⟨hregb, -⟩ := hw2
  have hinjι : Function.Injective (algebraMap B (Localization (nonZeroDivisors B))) :=
    IsLocalization.injective _ le_rfl
  have ha0 : a ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    refine hrega (?_ : a • x = a • 0)
    rw [smul_eq_mul, smul_eq_mul, mul_zero, mul_comm, hx]

  have L1 : ∀ (n : ℕ) (x : B), (∃ z, b ^ n * x = a * z) → ∃ z, x = a * z := by
    intro n
    induction n with
    | zero =>
      rintro x ⟨z, hz⟩
      exact ⟨z, by simpa using hz⟩
    | succ n ih =>
      rintro x ⟨z, hz⟩
      apply ih
      have hmem : b • (Submodule.Quotient.mk (b ^ n * x) : QuotSMulTop a B) = 0 := by
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
        exact ⟨z, Submodule.mem_top, by rw [smul_eq_mul, smul_eq_mul, ← hz]; ring⟩
      have h0 : (Submodule.Quotient.mk (b ^ n * x) : QuotSMulTop a B) = 0 :=
        hregb (show b • (Submodule.Quotient.mk (b ^ n * x) : QuotSMulTop a B) = b • (0 : QuotSMulTop a B) by
          rw [hmem, smul_zero])
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h0
      obtain ⟨w, -, hw⟩ := h0
      exact ⟨w, by rw [← hw, smul_eq_mul]⟩

  have L2 : ∀ (m n : ℕ) (x y : B), b ^ n * x = a ^ m * y → ∃ x', x = a ^ m * x' := by
    intro m
    induction m with
    | zero =>
      intro n x y _
      exact ⟨x, by simp⟩
    | succ m ih =>
      intro n x y h
      obtain ⟨x₁, rfl⟩ := L1 n x ⟨a ^ m * y, by rw [h]; ring⟩
      have h2 : b ^ n * x₁ = a ^ m * y := by
        refine hrega (?_ : a • (b ^ n * x₁) = a • (a ^ m * y))
        simp only [smul_eq_mul]
        calc a * (b ^ n * x₁) = b ^ n * (a * x₁) := by ring
          _ = a ^ (m + 1) * y := h
          _ = a * (a ^ m * y) := by ring
      obtain ⟨x₂, rfl⟩ := ih n x₁ y h2
      exact ⟨x₂, by ring⟩

  refine eq_bot_iff.2 fun r hr => ?_
  rw [Algebra.mem_bot]
  let C : Ideal B := Submodule.comap (LinearMap.toSpanSingleton B (Localization (nonZeroDivisors B)) r)
    (LinearMap.range (Algebra.linearMap B (Localization (nonZeroDivisors B))))
  have hC : ∀ s : B, s ∈ C ↔ ∃ x : B, algebraMap B (Localization (nonZeroDivisors B)) x =
      algebraMap B (Localization (nonZeroDivisors B)) s * r := by
    intro s
    simp only [C, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, LinearMap.mem_range,
      Algebra.linearMap_apply, Algebra.smul_def]
  have hrad : maximalIdeal B ≤ C.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hCP, hP⟩
    by_cases hPm : P = maximalIdeal B
    · exact hPm ▸ le_rfl
    · exfalso
      haveI := hP
      obtain ⟨s, hs𝔮, hs⟩ := ha P hPm r hr
      apply hs𝔮
      apply hCP
      rw [hC]
      obtain ⟨x, hx⟩ := RingHom.mem_range.1 hs
      exact ⟨x, hx⟩
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg C (IsNoetherian.noetherian _)
  have hpow : maximalIdeal B ^ N ≤ C := (Ideal.pow_right_mono hrad N).trans hN
  obtain ⟨x, hx⟩ := (hC _).1 (hpow (Ideal.pow_mem_pow ha𝔪 N))
  obtain ⟨y, hy⟩ := (hC _).1 (hpow (Ideal.pow_mem_pow hb𝔪 N))

  have hxy : b ^ N * x = a ^ N * y := by
    apply hinjι
    rw [map_mul, map_mul, hx, hy]
    ring
  obtain ⟨x', rfl⟩ := L2 N N x y hxy
  refine ⟨x', ?_⟩
  have hu : IsUnit (algebraMap B (Localization (nonZeroDivisors B)) (a ^ N)) :=
    IsLocalization.map_units _ ⟨a ^ N, pow_mem ha0 N⟩
  rw [map_mul] at hx
  exact hu.mul_left_cancel hx

end S_Subalgebra_eq_bot_of_moduleFinite_of_forall_ne_maximalIdeal_of_isRegular_pair
end P2MW
export P2MW.S_Subalgebra_eq_bot_of_moduleFinite_of_forall_ne_maximalIdeal_of_isRegular_pair (solution)
