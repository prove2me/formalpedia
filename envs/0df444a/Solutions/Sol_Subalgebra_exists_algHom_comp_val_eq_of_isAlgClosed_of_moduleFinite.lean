-- Prove2me | solution 1 for Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f65d6113-2f48-548a-9655-82d2598e9bff

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite

set_option autoImplicit false

universe u v w x

namespace E89C6

theorem extend {K : Type u} [CommRing K] {A : Type v} [CommRing A] [Algebra K A] [Module.Finite K A]
    (C : Subalgebra K A) (Ω : Type x) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ↥C →ₐ[K] Ω) : ∃ ν : A →ₐ[K] Ω, ν.comp C.val = h := by
  classical

  haveI : Algebra.IsIntegral K A := inferInstance
  haveI : Algebra.IsIntegral ↥C A :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := K) x).tower_top⟩

  let 𝔭 : Ideal ↥C := RingHom.ker h.toRingHom
  haveI h𝔭 : 𝔭.IsPrime := RingHom.ker_isPrime h.toRingHom
  obtain ⟨Q, -, hQprime, hQ⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral 𝔭 (⊥ : Ideal A) (by
      intro c hc
      rw [Ideal.mem_comap, Ideal.mem_bot] at hc
      show h.toRingHom c = 0
      have : (c : A) = 0 := hc
      have hc0 : c = 0 := Subtype.ext this
      rw [hc0, map_zero])
  haveI := hQprime

  let 𝔭' : Ideal ↥C := Q.comap (algebraMap ↥C A)
  have h𝔭' : 𝔭' = 𝔭 := hQ
  haveI : 𝔭'.IsPrime := by rw [h𝔭']; exact h𝔭
  haveI : IsDomain (↥C ⧸ 𝔭') := Ideal.Quotient.isDomain 𝔭'
  haveI : IsDomain (A ⧸ Q) := Ideal.Quotient.isDomain Q

  have hker : ∀ c ∈ 𝔭', h.toRingHom c = 0 := by
    intro c hc
    rw [h𝔭'] at hc
    exact hc
  let h' : ↥C ⧸ 𝔭' →+* Ω := Ideal.Quotient.lift 𝔭' h.toRingHom hker
  letI algΩ : Algebra (↥C ⧸ 𝔭') Ω := h'.toAlgebra
  have h'inj : Function.Injective h' :=
    RingHom.lift_injective_of_ker_le_ideal 𝔭' hker (fun c hc => by
      change h.toRingHom c = 0 at hc
      rw [h𝔭']
      exact hc)
  haveI : Module.IsTorsionFree (↥C ⧸ 𝔭') Ω := by
    refine Module.IsTorsionFree.mk fun r hr => ?_
    intro a b hab
    have hr0 : algebraMap (↥C ⧸ 𝔭') Ω r ≠ 0 := fun h0 =>
      hr.left.ne_zero (h'inj (by change algebraMap (↥C ⧸ 𝔭') Ω r = h' 0; rw [h0, map_zero]))
    have hab' : algebraMap (↥C ⧸ 𝔭') Ω r * a = algebraMap (↥C ⧸ 𝔭') Ω r * b := by
      simpa only [Algebra.smul_def] using hab
    exact mul_left_cancel₀ hr0 hab'

  haveI : FaithfulSMul (↥C ⧸ 𝔭') (A ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (↥C ⧸ 𝔭') (A ⧸ Q) := by
    refine Module.IsTorsionFree.mk fun r hr => ?_
    intro a b hab
    have hr0 : algebraMap (↥C ⧸ 𝔭') (A ⧸ Q) r ≠ 0 := fun h0 =>
      hr.left.ne_zero (Ideal.algebraMap_quotient_injective (by rw [h0, map_zero]))
    have hab' : algebraMap (↥C ⧸ 𝔭') (A ⧸ Q) r * a = algebraMap (↥C ⧸ 𝔭') (A ⧸ Q) r * b := by
      simpa only [Algebra.smul_def] using hab
    exact mul_left_cancel₀ hr0 hab'
  haveI : Algebra.IsIntegral (↥C ⧸ 𝔭') (A ⧸ Q) := inferInstance
  haveI : Algebra.IsAlgebraic (↥C ⧸ 𝔭') (A ⧸ Q) := Algebra.IsIntegral.isAlgebraic

  let ψ : (A ⧸ Q) →ₐ[↥C ⧸ 𝔭'] Ω := IsAlgClosed.lift
  let ν₀ : A →+* Ω := ψ.toRingHom.comp (Ideal.Quotient.mk Q)
  have hν₀C : ∀ c : ↥C, ν₀ (c : A) = h c := by
    intro c
    show ψ (Ideal.Quotient.mk Q (algebraMap ↥C A c)) = h c
    have h1 : Ideal.Quotient.mk Q (algebraMap ↥C A c) =
        algebraMap (↥C ⧸ 𝔭') (A ⧸ Q) (Ideal.Quotient.mk 𝔭' c) := rfl
    rw [h1, AlgHom.commutes]
    show h' (Ideal.Quotient.mk 𝔭' c) = h c
    rw [Ideal.Quotient.lift_mk]
    rfl
  refine ⟨{ ν₀ with commutes' := fun k => ?_ }, ?_⟩
  · show ν₀ (algebraMap K A k) = algebraMap K Ω k
    have : algebraMap K A k = ((algebraMap K ↥C k : ↥C) : A) := rfl
    rw [this, hν₀C, AlgHom.commutes]
  · apply AlgHom.ext
    intro c
    exact hν₀C c

end E89C6

theorem solution
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A]
    (C : Subalgebra R A) (Ω : Type w) [Field Ω] [Algebra R Ω] [IsAlgClosed Ω]
    (h : ↥C →ₐ[R] Ω) : ∃ ν : A →ₐ[R] Ω, ν.comp C.val = h :=
  E89C6.extend C Ω h

end S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
end P2MW
export P2MW.S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite (solution)
