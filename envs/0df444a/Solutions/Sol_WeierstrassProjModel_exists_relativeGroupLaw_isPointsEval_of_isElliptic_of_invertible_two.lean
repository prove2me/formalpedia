-- Prove2me | solution 1 for WeierstrassProjModel.exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_invertible_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b50519e1-8459-5f10-b479-47cfda7b80b2

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Theorems.Thm_WeierstrassProjModel_kw_bc_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smooth
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_relativeGroupLaw_exists
import Theorems.Thm_WeierstrassProjModel_kw_a2_exists_isPointsEval_of_addMorphism
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_invertible_two

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Invertible (2 : R)]
    (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic] :
    ∃ (hbc : ∀ (K : Type) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
      (G : RelativeGroupLaw R (projModelStrCR V))
      (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra R F],
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
          (V.baseChange F).toAffine.Point),
      IsPointsEval V G ev := by

  haveI hE : WeierstrassCurve.IsElliptic (V : WeierstrassCurve R) := ‹V.toAffine.IsElliptic›
  have hΔ : IsUnit (V : WeierstrassCurve R).Δ := hE.isUnit
  have hbc : ∀ (K : Type) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR V)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (V.baseChange K)) :=
    WeierstrassProjModel.kw_bc_baseChangeIso (R := R) V
  have hsm : Smooth (projModelStrCR V) := WeierstrassProjModel.projModelStrCR_smooth V
  have hgi : GeometricallyIntegral (projModelStrCR V) :=
    WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso (R := R) V hbc
  obtain ⟨hcov, hcompat, houter, G, hGmul, hGone, -⟩ :=
    WeierstrassProjModel.relativeGroupLaw_exists (R := R) V hsm hgi hΔ
  obtain ⟨ev, hev⟩ :=
    WeierstrassProjModel.kw_a2_exists_isPointsEval_of_addMorphism (R := R) V hΔ hcov hcompat houter G
      (fun t x y => hGmul t x y) (fun t => hGone t)
  exact ⟨hbc, G, ev, hev⟩

end S_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_invertible_two
end P2MW
export P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_invertible_two (solution)
