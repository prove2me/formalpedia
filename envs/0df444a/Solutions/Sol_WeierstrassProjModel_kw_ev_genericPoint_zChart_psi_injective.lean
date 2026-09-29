-- Prove2me | solution 1 for WeierstrassProjModel.kw_ev_genericPoint_zChart_psi_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2666171d-1e7b-58af-8b90-ee2509363e88

import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_isDomain_chart_of_isElliptic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_ev_genericPoint_zChart_psi_injective

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    haveI : Smooth (projModelStrCR W.toProjective) :=
      (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
    haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
      kw_hgi_geometricallyIntegral_of_baseChangeIso W
        (projModel_pullback_iso_baseChange W.toProjective)
    haveI : IsIntegral (projModelCR W.toProjective) :=
      GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
    letI : Algebra R (projModelCR W.toProjective).functionField :=
      (Spec.preimage ((projModelCR W.toProjective).fromSpecStalk
        (genericPoint (projModelCR W.toProjective)) ≫ projModelStrCR W.toProjective)).hom.toAlgebra
    ∀ (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R)) →ₐ[R] (projModelCR W.toProjective).functionField),
      (projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective))
        = Spec.map (CommRingCat.ofHom ψ.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3)
      → Function.Injective ψ := by

  haveI : Smooth (projModelStrCR W.toProjective) :=
    (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (projModel_pullback_iso_baseChange W.toProjective)
  haveI : IsLocallyNoetherian (projModelCR W.toProjective) :=
    LocallyOfFiniteType.isLocallyNoetherian (projModelStrCR W.toProjective)
  haveI : IsIntegral (projModelCR W.toProjective) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
  letI : Algebra R (projModelCR W.toProjective).functionField :=
    (Spec.preimage ((projModelCR W.toProjective).fromSpecStalk
      (genericPoint (projModelCR W.toProjective)) ≫ projModelStrCR W.toProjective)).hom.toAlgebra
  haveI : IsDomain (𝒜 (2 : Fin 3)) := isDomain_chart_of_isElliptic W (2 : Fin 3)
  intro ψ hfac
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne

  have hη : (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3)
      (Spec.map (CommRingCat.ofHom ψ.toRingHom)
        (IsLocalRing.closedPoint ((projModelCR W.toProjective).presheaf.stalk
          (genericPoint (projModelCR W.toProjective)))))
      = genericPoint (projModelCR W.toProjective) := by
    have h := (projModelCR W.toProjective).fromSpecStalk_closedPoint
      (x := genericPoint (projModelCR W.toProjective))
    rw [hfac, Scheme.Hom.comp_apply] at h
    exact h
  have ha_mem : a ∈ (Spec.map (CommRingCat.ofHom ψ.toRingHom)
        (IsLocalRing.closedPoint ((projModelCR W.toProjective).presheaf.stalk
          (genericPoint (projModelCR W.toProjective))))).asIdeal := by
    change ψ a ∈ (IsLocalRing.closedPoint ((projModelCR W.toProjective).presheaf.stalk
      (genericPoint (projModelCR W.toProjective)))).asIdeal
    rw [ha]
    exact Ideal.zero_mem _

  let q₀ : PrimeSpectrum (𝒜 (2 : Fin 3)) := ⟨⊥, Ideal.isPrime_bot⟩
  have hq₀ : q₀ ∈ PrimeSpectrum.basicOpen a := by
    rw [PrimeSpectrum.mem_basicOpen]
    exact fun h => hne ((Submodule.mem_bot (R := (𝒜 (2 : Fin 3)))).mp h)
  have hopen : IsOpen ((projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3) ''
      (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (𝒜 (2 : Fin 3))))) :=
    ((projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3)).isOpenEmbedding.isOpenMap
      _ (PrimeSpectrum.basicOpen a).isOpen
  have hηmem : genericPoint (projModelCR W.toProjective)
      ∈ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3) ''
        (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (𝒜 (2 : Fin 3)))) :=
    (genericPoint_specializes
      ((projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3) q₀)).mem_open
        hopen ⟨q₀, hq₀, rfl⟩
  obtain ⟨q', hq', hq'η⟩ := hηmem

  have heq : q' = Spec.map (CommRingCat.ofHom ψ.toRingHom)
      (IsLocalRing.closedPoint ((projModelCR W.toProjective).presheaf.stalk
        (genericPoint (projModelCR W.toProjective)))) :=
    ((projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3)).isOpenEmbedding.injective
      (hq'η.trans hη.symm)
  rw [← heq] at ha_mem
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hq' ha_mem

end

end S_WeierstrassProjModel_kw_ev_genericPoint_zChart_psi_injective
end P2MW
export P2MW.S_WeierstrassProjModel_kw_ev_genericPoint_zChart_psi_injective (solution)
