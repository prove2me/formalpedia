-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dvrParameterPrime_eq_spanX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:55:54.770693+00:00
-- url     : https://prove2.me/submissions/ab1d6c33-e53e-46d0-9c42-fb9f2b699f6e

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)
attribute [local instance] QEC.Coding.AlgebraicGeometry.dvrParameterPrime_isPrime
omit [IsDomain V]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [IsLocalRing V] (hπ : Irreducible π) :
    dvrParameterPrime k V π =
      Ideal.span ({Polynomial.X} : Set (Polynomial k)) := by
  have hp : IsLocalRing.residue V π = 0 :=
    (IsLocalRing.residue_eq_zero_iff π).mpr hπ.not_isUnit
  have hc : (IsLocalRing.residue V).comp (Polynomial.aeval π).toRingHom =
      (algebraMap k (IsLocalRing.ResidueField V)).comp
        (Polynomial.evalRingHom (0 : k)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.coe_evalRingHom, Polynomial.aeval_C, Polynomial.eval_C]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.coe_evalRingHom, Polynomial.aeval_X, Polynomial.eval_X, hp, map_zero]
  rw [dvrParameterPrime, ← IsLocalRing.ker_residue,
    RingHom.comap_ker, hc, RingHom.ker_comp_of_injective _
      (algebraMap k (IsLocalRing.ResidueField V)).injective]
  simpa using Polynomial.ker_evalRingHom (0 : k)
end QEC.Coding.AlgebraicGeometry
