-- Prove2me | solution 1 for WeierstrassProjModel.kw_ev_genericPoint_zChart_factor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/bcd97894-0045-55ef-96a8-ffd2f896fbe5

import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_pointEval
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_nontrivial_chart_of_isElliptic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_ev_genericPoint_zChart_factor

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
    ∃ (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R)) →ₐ[R] (projModelCR W.toProjective).functionField),
      (projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective))
        = Spec.map (CommRingCat.ofHom ψ.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3) := by

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

  let ι₂ := (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3)

  haveI : Nontrivial (𝒜 (2 : Fin 3)) := nontrivial_chart_of_isElliptic W (2 : Fin 3)
  obtain ⟨y, hy⟩ : (Set.range ⇑ι₂).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of (𝒜 (2 : Fin 3)))))
    exact ⟨ι₂.base x, x, rfl⟩
  have hηmem : genericPoint (projModelCR W.toProjective) ∈ Set.range ⇑ι₂ :=
    (genericPoint_specializes y).mem_open (IsOpenImmersion.isOpen_range ι₂) hy

  have hrange : Set.range ⇑((projModelCR W.toProjective).fromSpecStalk
      (genericPoint (projModelCR W.toProjective))) ⊆ Set.range ⇑ι₂ := by
    rw [Scheme.range_fromSpecStalk]
    exact fun z hz => hz.mem_open (IsOpenImmersion.isOpen_range ι₂) hηmem

  let g := IsOpenImmersion.lift ι₂
    ((projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective))) hrange
  have hfac : g ≫ ι₂ = (projModelCR W.toProjective).fromSpecStalk
      (genericPoint (projModelCR W.toProjective)) :=
    IsOpenImmersion.lift_fac ι₂ _ hrange

  let φ₀ : CommRingCat.of (𝒜 (2 : Fin 3)) ⟶ (projModelCR W.toProjective).functionField :=
    Spec.preimage g
  have hg : Spec.map φ₀ = g := Spec.map_preimage g

  have hstr : ι₂ ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 (2 : Fin 3)))) :=
    kw_pbac_awayι_comp_projModelStrCR R W.toProjective (2 : Fin 3)

  have hcomm' : CommRingCat.ofHom (algebraMap R (𝒜 (2 : Fin 3))) ≫ φ₀
      = Spec.preimage ((projModelCR W.toProjective).fromSpecStalk
          (genericPoint (projModelCR W.toProjective)) ≫ projModelStrCR W.toProjective) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hg, Spec.map_preimage, ← hfac, Category.assoc]
    exact congrArg (g ≫ ·) hstr.symm

  refine ⟨{ φ₀.hom with
      commutes' := fun r => congrArg (fun f => CommRingCat.Hom.hom f r) hcomm' }, ?_⟩
  show (projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective))
    = Spec.map φ₀ ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3)
  rw [hg]
  exact hfac.symm

end

end S_WeierstrassProjModel_kw_ev_genericPoint_zChart_factor
end P2MW
export P2MW.S_WeierstrassProjModel_kw_ev_genericPoint_zChart_factor (solution)
