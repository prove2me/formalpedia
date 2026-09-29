-- Prove2me | solution 1 for WeierstrassProjModel.isDomain_chartTensor_of_isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c98059fb-15b8-5d8e-b88e-9a187ae665bd

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_nontrivial_chartTensor_of_isElliptic
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i j : Fin 3) :
    IsDomain ((𝒜 i) ⊗[R] (𝒜 j)) := by
  haveI hnt : Nontrivial ((𝒜 i) ⊗[R] (𝒜 j)) :=
    WeierstrassProjModel.nontrivial_chartTensor_of_isElliptic W i j
  haveI hne : Nonempty (Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j)))) := inferInstance
  haveI hsm : Smooth (π) :=
    (WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI hgi : GeometricallyIntegral (π) :=
    WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (WeierstrassProjModel.projModel_pullback_iso_baseChange W.toProjective)
  haveI : IsIntegral (projModelCR W.toProjective) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (π)
  haveI : IsLocallyNoetherian (projModelCR W.toProjective) :=
    LocallyOfFiniteType.isLocallyNoetherian (π)
  haveI : GeometricallyIntegral (pullback.fst (π) (π)) :=
    MorphismProperty.pullback_fst _ _ hgi
  haveI : IsIntegral ↑(pullback (π) (π)) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst (π) (π))
  haveI hI : IsIntegral (Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j)))) :=
    isIntegral_of_isOpenImmersion
      ((kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j))

  haveI : IsDomain ((Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j)))).presheaf.obj (Opposite.op ⊤)) :=
    inferInstance
  exact ((Scheme.ΓSpecIso (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j)))).symm.commRingCatIsoToRingEquiv
    ).injective.isDomain _

end S_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic
end P2MW
export P2MW.S_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic (solution)
