-- Prove2me | solution 1 for Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/55c31cb3-427e-5e2f-b595-dc95000233d4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

theorem solution {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] [Module.Finite R A]
    (S : Subalgebra R A) (k : Type*) [Field k] [IsAlgClosed k] [Algebra R k] (φ : ↥S →ₐ[R] k) :
    ∃ ψ : A →ₐ[R] k, ψ.comp S.val = φ := by
  classical

  haveI : Module.Finite S A := Module.Finite.of_restrictScalars_finite R S A
  haveI : Algebra.IsIntegral S A := Algebra.IsIntegral.of_finite S A

  let 𝔭 : Ideal S := RingHom.ker (φ : S →+* k)
  haveI h𝔭 : 𝔭.IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, -, hQ, hQover⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭 (⊥ : Ideal A)
    (Ideal.comap_bot_le_of_injective _ Subtype.val_injective)
  haveI := hQ
  haveI hLO : Q.LiesOver 𝔭 := ⟨hQover.symm⟩

  let φbar : (S ⧸ 𝔭) →ₐ[R] k := Ideal.Quotient.liftₐ 𝔭 φ (fun a ha => ha)
  letI : Algebra (S ⧸ 𝔭) k := φbar.toRingHom.toAlgebra
  haveI : IsScalarTower R (S ⧸ 𝔭) k := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R k r = φbar (algebraMap R (S ⧸ 𝔭) r)
    rw [AlgHom.commutes]
  have hinj : Function.Injective (algebraMap (S ⧸ 𝔭) k) := by
    show Function.Injective φbar
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  haveI : IsDomain (S ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  haveI : IsDomain (A ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Module.IsTorsionFree (S ⧸ 𝔭) k := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
  haveI : Module.IsTorsionFree (S ⧸ 𝔭) (A ⧸ Q) :=
    (Module.isTorsionFree_iff_faithfulSMul).mpr (Ideal.Quotient.instFaithfulSMul Q 𝔭)
  haveI : Algebra.IsIntegral (S ⧸ 𝔭) (A ⧸ Q) := Ideal.Quotient.algebra_isIntegral_of_liesOver Q 𝔭
  haveI : Nontrivial (S ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr h𝔭.ne_top
  haveI : Algebra.IsAlgebraic (S ⧸ 𝔭) (A ⧸ Q) := Algebra.IsIntegral.isAlgebraic

  let ψ' : (A ⧸ Q) →ₐ[S ⧸ 𝔭] k := IsAlgClosed.lift
  refine ⟨(ψ'.restrictScalars R).comp (Ideal.Quotient.mkₐ R Q), ?_⟩
  apply AlgHom.ext; intro s
  show ψ' (Ideal.Quotient.mk Q (s : A)) = φ s
  have h1 : Ideal.Quotient.mk Q (s : A) = algebraMap (S ⧸ 𝔭) (A ⧸ Q) (Ideal.Quotient.mk 𝔭 s) := rfl
  rw [h1, AlgHom.commutes]
  rfl

end S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed
end P2MW
export P2MW.S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed (solution)
