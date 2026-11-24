-- Prove2me | solution 1 for comap_span_galRestrict_eq_of_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:52.961803+00:00
-- url     : https://prove2.me/submissions/63c249bf-80b4-4668-9c95-5edabdb2f203

module
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_Hilbert94
public import Theorems.Thm_Hilbert92


set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField
variable {K : Type} [Field K]
open Polynomial Module
variable {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L]
include hσ
theorem _root_.solution (β : B) (η : Bˣ)
    (hβ : η * (galRestrict A K L B σ) β = β) (σ' : L ≃ₐ[K] L) :
    (Ideal.span {β}).comap (galRestrict A K L B σ') = Ideal.span {β} := by
  suffices (Ideal.span {β}).map
      (galRestrict A K L B σ'⁻¹).toRingEquiv.toRingHom = Ideal.span {β} by
    rwa [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv, map_inv] at this
  apply_fun (Ideal.span {·}) at hβ
  rw [← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.mpr η.isUnit,
    ← Ideal.one_eq_top, one_mul, ← Set.image_singleton, ← Ideal.map_span] at hβ
  change Ideal.map (galRestrict A K L B σ : B →+* B) _ = _ at hβ
  generalize σ'⁻¹ = τ
  obtain ⟨n, rfl : σ ^ n = τ⟩ := mem_powers_iff_mem_zpowers.mpr (hσ τ)
  rw [map_pow]
  induction n with
  | zero =>
    simp only [pow_zero, RingEquiv.toRingHom_eq_coe]
    exact Ideal.map_id _
  | succ n IH =>
    simp only [RingEquiv.toRingHom_eq_coe, pow_succ] at IH ⊢
    conv_lhs at IH => rw [← hβ, Ideal.map_map]
    exact IH
