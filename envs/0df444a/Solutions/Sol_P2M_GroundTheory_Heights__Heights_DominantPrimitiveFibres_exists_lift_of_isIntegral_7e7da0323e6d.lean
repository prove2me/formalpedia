-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_isIntegral_7e7da0323e6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:44.16686+00:00
-- url     : https://prove2.me/submissions/68ba3ba3-fc67-4499-a18e-283aa37d033f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDominantFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDominantPrimitiveFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
open GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
namespace GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
theorem _root_.solution {R' B' : Type*} [CommRing R'] [CommRing B'] [Algebra R' B']
    [Algebra.IsIntegral R' B'] (φ : R' →+* ℂ) (hφ : Function.Surjective φ)
    (hker : RingHom.ker (algebraMap R' B') ≤ RingHom.ker φ) :
    ∃ ψ : B' →+* ℂ, ψ.comp (algebraMap R' B') = φ := by
  have hmax : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφ
  obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B') _ hker
  have := hP
  have hmax' : (P.comap (algebraMap R' B')).IsMaximal := hPc ▸ hmax
  letI : Field (R' ⧸ P.comap (algebraMap R' B')) := Ideal.Quotient.field _
  letI : Field (B' ⧸ P) := Ideal.Quotient.field P
  let e : (R' ⧸ P.comap (algebraMap R' B')) ≃+* ℂ :=
    (Ideal.quotEquivOfEq hPc).trans (RingHom.quotientKerEquivOfSurjective hφ)
  letI : Algebra (R' ⧸ P.comap (algebraMap R' B')) ℂ := e.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic (R' ⧸ P.comap (algebraMap R' B')) (B' ⧸ P) :=
    Algebra.IsIntegral.isAlgebraic
  let f : (B' ⧸ P) →ₐ[R' ⧸ P.comap (algebraMap R' B')] ℂ := IsAlgClosed.lift
  refine ⟨f.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩
  ext r
  have h1 : Ideal.Quotient.mk P (algebraMap R' B' r) =
      algebraMap (R' ⧸ P.comap (algebraMap R' B')) (B' ⧸ P) (Ideal.Quotient.mk _ r) := rfl
  rw [RingHom.comp_apply, RingHom.comp_apply, h1, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, f.commutes]
  change e (Ideal.Quotient.mk _ r) = φ r
  simp [e, Ideal.quotEquivOfEq_mk]
end GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
