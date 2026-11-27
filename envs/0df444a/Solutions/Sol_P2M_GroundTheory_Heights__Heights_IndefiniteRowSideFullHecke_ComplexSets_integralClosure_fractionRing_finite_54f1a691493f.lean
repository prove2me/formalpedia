-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_integralClosure_fractionRing_finite_54f1a691493f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:50.678282+00:00
-- url     : https://prove2.me/submissions/ddd36025-9250-4d5d-b8cf-c5d2d4f1aae8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelExists
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NonemptyNormalModelOfPresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [Algebra ℂ R]
    [Algebra.FiniteType ℂ R] : Module.Finite R (integralClosure R (FractionRing R)) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ R
  let _ : Algebra (MvPolynomial (Fin s) ℂ) R := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin s) ℂ) R := hfin
  have : FaithfulSMul (MvPolynomial (Fin s) ℂ) R :=
    (faithfulSMul_iff_algebraMap_injective _ R).mpr hinj
  have : Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) R := inferInstance
  have : FiniteDimensional (FractionRing (MvPolynomial (Fin s) ℂ)) (FractionRing R) := inferInstance
  have : CharZero (FractionRing (MvPolynomial (Fin s) ℂ)) :=
    charZero_of_injective_algebraMap (algebraMap ℂ _).injective
  have : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin s) ℂ)) (FractionRing R) := inferInstance
  have : IsIntegralClosure (integralClosure R (FractionRing R)) (MvPolynomial (Fin s) ℂ)
      (FractionRing R) :=
    ⟨Subtype.val_injective, fun {x} =>
      ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸
        isIntegral_trans (R := MvPolynomial (Fin s) ℂ) (A := R) _ ((integralClosure.isIntegral y).map
          (IsScalarTower.toAlgHom R (integralClosure R (FractionRing R)) (FractionRing R)))⟩⟩
  have := IsIntegralClosure.finite (MvPolynomial (Fin s) ℂ) (FractionRing (MvPolynomial (Fin s) ℂ))
    (FractionRing R) (integralClosure R (FractionRing R))
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) ℂ) R _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
