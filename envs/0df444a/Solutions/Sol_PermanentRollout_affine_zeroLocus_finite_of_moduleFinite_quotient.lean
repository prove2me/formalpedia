-- Prove2me | solution 1 for PermanentRollout.affine_zeroLocus_finite_of_moduleFinite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/094fbecf-6311-4dde-b3fc-8329e802f005

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
    {ι : Type*}
    (I : Ideal (MvPolynomial ι ℂ))
    (hfinite : Module.Finite ℂ (MvPolynomial ι ℂ ⧸ I)) :
    (MvPolynomial.zeroLocus ℂ I).Finite := by
  classical
  let A := MvPolynomial ι ℂ ⧸ I
  let Z := {x : ι → ℂ // x ∈ MvPolynomial.zeroLocus ℂ I}
  letI : Module.Finite ℂ A := hfinite
  letI : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  let pointEval (x : Z) : A →ₐ[ℂ] ℂ :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval (x : ι → ℂ))
      (fun p hp => (MvPolynomial.mem_zeroLocus_iff.mp x.property) p hp)
  have hsurj (x : Z) : Function.Surjective (pointEval x) := by
    intro c
    refine ⟨algebraMap ℂ A c, ?_⟩
    exact (pointEval x).commutes c
  let pointIdeal (x : Z) : MaximalSpectrum A :=
    ⟨RingHom.ker (pointEval x).toRingHom,
      RingHom.ker_isMaximal_of_surjective
        (pointEval x).toRingHom (hsurj x)⟩
  have hinj : Function.Injective pointIdeal := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hker : RingHom.ker (pointEval x).toRingHom =
        RingHom.ker (pointEval y).toRingHom :=
      congrArg MaximalSpectrum.asIdeal hxy
    have hxmem :
        Ideal.Quotient.mk I
            (MvPolynomial.X i - MvPolynomial.C ((x : ι → ℂ) i)) ∈
          RingHom.ker (pointEval x).toRingHom := by
      change MvPolynomial.aeval (x : ι → ℂ)
        (MvPolynomial.X i - MvPolynomial.C ((x : ι → ℂ) i)) = 0
      simp
    have hymem :
        Ideal.Quotient.mk I
            (MvPolynomial.X i - MvPolynomial.C ((x : ι → ℂ) i)) ∈
          RingHom.ker (pointEval y).toRingHom := hker ▸ hxmem
    change MvPolynomial.aeval (y : ι → ℂ)
      (MvPolynomial.X i - MvPolynomial.C ((x : ι → ℂ) i)) = 0 at hymem
    have heq : (y : ι → ℂ) i - (x : ι → ℂ) i = 0 := by
      simpa using hymem
    exact (sub_eq_zero.mp heq).symm
  exact Set.finite_coe_iff.mp (Finite.of_injective pointIdeal hinj)
end PermanentRollout
