-- Prove2me | solution 1 for ValuationSubring.forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7cf0528e-78a9-590f-bb64-6ac1732c265b

import Mathlib
import Theorems.Thm_IntermediateField_finiteDimensional_and_finrank_le_and_isSeparable_of_pow_eq_of_adjoin_simple_eq_top
import Theorems.Thm_Ideal_dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime
import Theorems.Thm_IsDiscreteValuationRing_exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx
import Theorems.Thm_IsDiscreteValuationRing_forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (n : ℕ) (hn : 0 < n) (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (a : E) (b : F) (hab : a ^ n = algebraMap F E b)
    (hgen : IntermediateField.adjoin F ({a} : Set E) = ⊤)
    (O : ValuationSubring F) [IsDiscreteValuationRing ↥O]
    (ϖ : ↥O) (hϖ : Irreducible ϖ) (u : (↥O)ˣ) (m : ℤ) (hm : IsCoprime m (n : ℤ))
    (hb : b = ((u : ↥O) : F) * ((ϖ : ↥O) : F) ^ m) :
    (∀ O₁ O₂ : ValuationSubring E,
        O₁.comap (algebraMap F E) = O → O₂.comap (algebraMap F E) = O → O₁ = O₂) ∧
    (∃ O' : ValuationSubring E, O'.comap (algebraMap F E) = O ∧
      (∀ e : ↥O', ∃ f : ↥O, (e : E) - algebraMap F E (f : F) ∈ O'.nonunits) ∧
      (∃ (π : ↥O') (v : (↥O')ˣ), Irreducible π ∧
        algebraMap F E ((ϖ : ↥O) : F) = ((v : ↥O') : E) * ((π : ↥O') : E) ^ n)) := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩

  letI : Algebra ↥O E := ((algebraMap F E).comp (algebraMap ↥O F)).toAlgebra
  haveI : IsScalarTower ↥O F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halg : ∀ x : ↥O, algebraMap ↥O E x = algebraMap F E (x : F) := fun _ => rfl

  have hnF : (n : F) ≠ 0 := (hζ.neZero' (n := n)).out
  have hϖ0 : ((ϖ : ↥O) : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hb0 : b ≠ 0 := by
    rw [hb]
    exact mul_ne_zero (fun h => (u.isUnit.ne_zero) (Subtype.ext h)) (zpow_ne_zero _ hϖ0)
  obtain ⟨hfd, hdeg, hsep⟩ :=
    IntermediateField.finiteDimensional_and_finrank_le_and_isSeparable_of_pow_eq_of_adjoin_simple_eq_top
      n hnF a b hb0 hab hgen
  haveI := hfd
  haveI := hsep

  haveI : IsDedekindDomain ↥(integralClosure ↥O E) := integralClosure.isDedekindDomain ↥O F E
  haveI : Module.Finite ↥O ↥(integralClosure ↥O E) := IsIntegralClosure.finite ↥O F E ↥(integralClosure ↥O E)
  haveI : IsFractionRing ↥(integralClosure ↥O E) E := integralClosure.isFractionRing_of_finite_extension F E

  have hab' : a ^ n = algebraMap ↥O E (u : ↥O) * algebraMap ↥O E ϖ ^ m := by
    rw [hab, hb, map_mul, map_zpow₀, halg, halg]
  obtain ⟨𝔓, h𝔓p, h𝔓0, hover, he, hf, -⟩ :=
    IsDiscreteValuationRing.exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx
      F E n hdeg (fun 𝔓 _ h0 hlo => by
        haveI := hlo
        exact Ideal.dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime ϖ hϖ u m n hn hm a hab' 𝔓 h0)
  haveI := h𝔓p

  obtain ⟨huniq, hOW, hmW, hres, hram⟩ :=
    IsDiscreteValuationRing.forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton
      E ϖ hϖ n 𝔓 h𝔓0 hover he hf _ rfl
  set W := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E
    (⟨𝔓, h𝔓p, h𝔓0⟩ : IsDedekindDomain.HeightOneSpectrum ↥(integralClosure ↥O E)) with hWdef

  have key₁ : ∀ W' : ValuationSubring E, W'.comap (algebraMap F E) = O →
      (∀ x : ↥O, algebraMap ↥O E x ∈ W') ∧
        (∀ x ∈ IsLocalRing.maximalIdeal ↥O, algebraMap ↥O E x ∈ W'.nonunits) := by
    intro W' hW'
    have hmem : ∀ y : F, y ∈ O ↔ algebraMap F E y ∈ W' := fun y => by
      rw [← hW']; rfl
    refine ⟨fun x => (hmem x).mp x.2, fun x hx => ?_⟩
    rw [ValuationSubring.mem_nonunits_iff]
    have hxW : algebraMap F E (x : F) ∈ W' := (hmem x).mp x.2
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have hxF0 : (x : F) ≠ 0 := fun h => hx0 (Subtype.ext h)
    refine lt_of_le_of_ne ((W'.valuation_le_one_iff _).mpr hxW) fun hval => ?_

    have hval' : W'.valuation (algebraMap F E (x : F)) = 1 := by
      rw [← halg]
      exact hval
    have hinvW : algebraMap F E (x : F)⁻¹ ∈ W' := by
      apply (W'.valuation_le_one_iff _).mp
      rw [map_inv₀ (algebraMap F E), map_inv₀ W'.valuation, hval', inv_one]
    have hinvO : (x : F)⁻¹ ∈ O := (hmem _).mpr hinvW
    have hunit : IsUnit x := by
      refine ⟨⟨x, ⟨(x : F)⁻¹, hinvO⟩, Subtype.ext (mul_inv_cancel₀ hxF0), Subtype.ext (inv_mul_cancel₀ hxF0)⟩, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp hx hunit
  have key₂ : ∀ W' : ValuationSubring E, (∀ x : ↥O, algebraMap ↥O E x ∈ W') →
      (∀ x : ↥O, algebraMap ↥O E x ∈ W'.nonunits ↔ x ∈ IsLocalRing.maximalIdeal ↥O) →
      W'.comap (algebraMap F E) = O := by
    intro W' h1 h2
    ext y
    change algebraMap F E y ∈ W' ↔ y ∈ O
    refine ⟨fun hy => ?_, fun hy => h1 ⟨y, hy⟩⟩
    by_contra hyO
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hyO O.zero_mem
    have hinvO : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hyO
    have hinv𝔪 : (⟨y⁻¹, hinvO⟩ : ↥O) ∈ IsLocalRing.maximalIdeal ↥O := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      apply hyO
      obtain ⟨w, hw⟩ := hu

      have hwF : ((w : ↥O) : F) = y⁻¹ := congrArg Subtype.val hw
      have hy' : y = (((w⁻¹ : (↥O)ˣ) : ↥O) : F) := by
        have h3 : ((w : ↥O) : F) * (((w⁻¹ : (↥O)ˣ) : ↥O) : F) = 1 := by
          rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
        rw [hwF] at h3
        calc y = y * (y⁻¹ * (((w⁻¹ : (↥O)ˣ) : ↥O) : F)) := by rw [h3, mul_one]
          _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hy0, one_mul]
      rw [hy']
      exact ((w⁻¹ : (↥O)ˣ) : ↥O).2
    have hlt := (h2 _).mpr hinv𝔪
    rw [ValuationSubring.mem_nonunits_iff] at hlt
    have hle : W'.valuation (algebraMap F E y) ≤ 1 := (W'.valuation_le_one_iff _).mpr hy
    have : W'.valuation (algebraMap F E y * algebraMap F E y⁻¹) < 1 := by
      rw [map_mul]
      calc W'.valuation (algebraMap F E y) * W'.valuation (algebraMap F E y⁻¹)
          ≤ 1 * W'.valuation (algebraMap F E y⁻¹) := mul_le_mul_left hle _
        _ < 1 := by rw [one_mul]; exact hlt
    rw [← map_mul, mul_inv_cancel₀ hy0, map_one, map_one] at this
    exact lt_irrefl _ this
  refine ⟨fun O₁ O₂ h₁ h₂ => huniq O₁ O₂ (key₁ O₁ h₁).1 (key₁ O₁ h₁).2 (key₁ O₂ h₂).1 (key₁ O₂ h₂).2,
    W, key₂ W hOW hmW, fun e => ?_, ?_⟩
  · obtain ⟨f, hf'⟩ := hres e
    exact ⟨f, hf'⟩
  · obtain ⟨π, v, hπ, hϖπ⟩ := hram
    exact ⟨π, v, hπ, hϖπ⟩

end S_ValuationSubring_forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime
end P2MW
export P2MW.S_ValuationSubring_forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime (solution)
