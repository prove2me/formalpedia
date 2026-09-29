-- Prove2me | solution 1 for RingHom.exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/287b9baf-b242-5873-a036-e56ecd68b0db

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed

set_option autoImplicit false

theorem solution
    {B₁ B Ω : Type*} [CommRing B₁] [CommRing B] [Field Ω] [IsAlgClosed Ω]
    (f : B₁ →+* B) (hf : f.IsIntegral)
    (φ₁ : B₁ →+* Ω) (y : Ideal B) [y.IsPrime]
    (hy : y.comap f = RingHom.ker φ₁) :
    ∃ φ : B →+* Ω, φ.comp f = φ₁ ∧ RingHom.ker φ = y := by
  letI : Algebra B₁ B := f.toAlgebra
  haveI : Algebra.IsIntegral B₁ B := ⟨hf⟩

  set P : Ideal B₁ := y.comap (algebraMap B₁ B) with hPdef
  have hPy : P = RingHom.ker φ₁ := hy
  haveI : IsDomain (B ⧸ y) := Ideal.Quotient.isDomain y
  haveI : IsDomain (B₁ ⧸ P) := Ideal.Quotient.isDomain P
  haveI : Algebra.IsIntegral (B₁ ⧸ P) (B ⧸ y) := Algebra.IsIntegral.quotient
  haveI : Module.IsTorsionFree (B₁ ⧸ P) (B ⧸ y) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Ideal.algebraMap_quotient_injective

  have hP : ∀ a : B₁, a ∈ P → φ₁ a = 0 := fun a ha => by
    rw [hPy] at ha
    exact RingHom.mem_ker.mp ha
  let ψ : B₁ ⧸ P →+* Ω := Ideal.Quotient.lift P φ₁ hP
  have hψinj : Function.Injective ψ := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_quotient_lift, ← hPy]
    exact Ideal.map_quotient_self P
  letI : Algebra (B₁ ⧸ P) Ω := ψ.toAlgebra
  haveI : Module.IsTorsionFree (B₁ ⧸ P) Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hψinj

  let Φ : (B ⧸ y) →ₐ[B₁ ⧸ P] Ω := IsAlgClosed.lift

  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hker : RingHom.ker (Φ : (B ⧸ y) →+* Ω) = ⊥ := by
      refine Ideal.eq_bot_of_comap_eq_bot (R := B₁ ⧸ P) ?_
      ext r
      rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      show Φ (algebraMap (B₁ ⧸ P) (B ⧸ y) r) = 0 ↔ r = 0
      rw [Φ.commutes, RingHom.algebraMap_toAlgebra, map_eq_zero_iff ψ hψinj]
    have : x ∈ RingHom.ker (Φ : (B ⧸ y) →+* Ω) := (RingHom.mem_ker).mpr hx
    rw [hker] at this
    exact (Submodule.mem_bot _).mp this
  refine ⟨(Φ : (B ⧸ y) →+* Ω).comp (Ideal.Quotient.mk y), ?_, ?_⟩
  · ext b
    show Φ (Ideal.Quotient.mk y (f b)) = φ₁ b
    have : Ideal.Quotient.mk y (f b) = algebraMap (B₁ ⧸ P) (B ⧸ y) (Ideal.Quotient.mk P b) := rfl
    rw [this, Φ.commutes]
    show ψ (Ideal.Quotient.mk P b) = φ₁ b
    exact Ideal.Quotient.lift_mk P φ₁ hP
  · ext b
    rw [RingHom.mem_ker, RingHom.comp_apply]
    show Φ (Ideal.Quotient.mk y b) = 0 ↔ b ∈ y
    rw [map_eq_zero_iff _ hΦinj, Ideal.Quotient.eq_zero_iff_mem]

end S_RingHom_exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
end P2MW
export P2MW.S_RingHom_exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed (solution)
