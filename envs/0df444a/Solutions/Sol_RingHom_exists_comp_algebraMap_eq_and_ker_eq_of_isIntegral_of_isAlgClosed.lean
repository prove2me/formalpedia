-- Prove2me | solution 1 for RingHom.exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/7361bde7-07a5-54b6-8290-bb1dfffcf703

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed

open Ideal in
theorem solution
    {R S K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    [Field K] [IsAlgClosed K] (χ : R →+* K)
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.comap (algebraMap R S) = RingHom.ker χ) :
    ∃ χ' : S →+* K, χ'.comp (algebraMap R S) = χ ∧ RingHom.ker χ' = Q := by
  classical
  set P : Ideal R := Q.comap (algebraMap R S) with hPdef
  haveI hP : P.IsPrime := Ideal.IsPrime.comap _
  have hle : ∀ a ∈ P, χ a = 0 := fun a ha => RingHom.mem_ker.mp (hQ ▸ ha)

  let ψ : R ⧸ P →+* K := Ideal.Quotient.lift P χ hle
  have hψinj : Function.Injective ψ :=
    RingHom.lift_injective_of_ker_le_ideal P hle hQ.ge
  letI : Algebra (R ⧸ P) K := ψ.toAlgebra
  haveI : FaithfulSMul (R ⧸ P) K :=
    (faithfulSMul_iff_algebraMap_injective _ K).mpr hψinj
  haveI : FaithfulSMul (R ⧸ P) (S ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  haveI : Algebra.IsIntegral (R ⧸ P) (S ⧸ Q) := Algebra.IsIntegral.quotient
  haveI : Module.IsTorsionFree (R ⧸ P) (S ⧸ Q) :=
    @FaithfulSMul.to_isTorsionFree _ _ _ _ _ _ inferInstance inferInstance
  haveI : Module.IsTorsionFree (R ⧸ P) K :=
    @FaithfulSMul.to_isTorsionFree _ _ _ _ _ _ inferInstance inferInstance
  haveI : Algebra.IsAlgebraic (R ⧸ P) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic

  let θ : (S ⧸ Q) →ₐ[R ⧸ P] K := IsAlgClosed.lift
  refine ⟨θ.toRingHom.comp (Ideal.Quotient.mk Q), ?_, ?_⟩
  · ext a
    change θ (Ideal.Quotient.mk Q (algebraMap R S a)) = χ a
    have h1 : Ideal.Quotient.mk Q (algebraMap R S a)
        = algebraMap (R ⧸ P) (S ⧸ Q) (Ideal.Quotient.mk P a) := rfl
    rw [h1, θ.commutes]
    exact Ideal.Quotient.lift_mk P χ _
  ·
    have hker : RingHom.ker θ.toRingHom = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := R ⧸ P)
      rw [eq_bot_iff]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker] at hx
      change θ (algebraMap (R ⧸ P) (S ⧸ Q) x) = 0 at hx
      rw [θ.commutes] at hx
      exact (Ideal.mem_bot).mpr (hψinj (by rw [map_zero]; exact hx))
    rw [← RingHom.comap_ker, hker, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

end S_RingHom_exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
end P2MW
export P2MW.S_RingHom_exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed (solution)
