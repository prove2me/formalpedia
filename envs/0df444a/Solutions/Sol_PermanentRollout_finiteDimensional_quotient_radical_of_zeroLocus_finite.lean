-- Prove2me | solution 1 for PermanentRollout.finiteDimensional_quotient_radical_of_zeroLocus_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/3fcc06ba-c771-4905-9aa6-0a5a368d2498

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι]
    (I : Ideal (MvPolynomial ι ℂ))
    (hfinite : (MvPolynomial.zeroLocus ℂ I).Finite) :
    Module.Finite ℂ (MvPolynomial ι ℂ ⧸ I.radical) := by
  classical
  let Z : Type _ := {x : ι → ℂ // x ∈ MvPolynomial.zeroLocus ℂ I}
  letI : Finite Z := Set.finite_coe_iff.mpr hfinite
  have hvanish (x : Z) (p : MvPolynomial ι ℂ)
      (hp : p ∈ I.radical) : MvPolynomial.aeval (x : ι → ℂ) p = 0 := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)] at hp
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp hp) x x.property
  let evalAt (x : Z) : (MvPolynomial ι ℂ ⧸ I.radical) →ₐ[ℂ] ℂ :=
    Ideal.Quotient.liftₐ I.radical
      (MvPolynomial.aeval (x : ι → ℂ)) (hvanish x)
  let E : (MvPolynomial ι ℂ ⧸ I.radical) →ₗ[ℂ] (Z → ℂ) :=
    LinearMap.pi fun x => (evalAt x).toLinearMap
  have hinj : Function.Injective E := by
    intro a b hab
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro x hx
    have hvalue := congr_fun hab (⟨x, hx⟩ : Z)
    change MvPolynomial.aeval x p = MvPolynomial.aeval x q at hvalue
    rw [map_sub, hvalue, sub_self]
  exact Module.Finite.of_injective E hinj
end PermanentRollout
