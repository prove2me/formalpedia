-- Prove2me | solution 1 for WeierstrassProjModel.exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/dbdb8f61-9bf2-5a6b-8dd9-017be46113c9

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Theorems.Thm_WeierstrassProjModel_kw_bc_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain
import Theorems.Thm_WeierstrassProjModel_exists_perChart_addMorphism_of_thirdLaw_nineCoverage
import Theorems.Thm_WeierstrassProjModel_exists_addMorphism_of_perChart_addMorphism_pin
import Theorems.Thm_WeierstrassProjModel_exists_relativeGroupLaw_mul_eq_one_eq_zeroSect_of_addMorphism_sixU_pin
import Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_of_addMorphism_sixU_pin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in
set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
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

  obtain ⟨u₃, toE₃, hcov₉, hcompat₃⟩ :=
    WeierstrassProjModel.exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain (R := R) V

  obtain ⟨pcm, hpin⟩ :=
    WeierstrassProjModel.exists_perChart_addMorphism_of_thirdLaw_nineCoverage (R := R) V
      u₃ toE₃ hcov₉ hcompat₃

  obtain ⟨m, hm_over, hm_chart⟩ :=
    WeierstrassProjModel.exists_addMorphism_of_perChart_addMorphism_pin (R := R) V pcm hpin
  have hmpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap V i j l
        ≫ (kwProjPullbackChartIsoCR R V i j).inv
        ≫ (kwProjPullbackOpenCoverCR R V).f (i, j) ≫ m
      = kw_lrSixU_toE V i j l := fun i j l =>
    .trans (congrArg (kw_lrSixU_locMap V i j l ≫ ·)
      ((Iso.inv_comp_eq (kwProjPullbackChartIsoCR R V i j)).mpr
        (hm_chart (i, j)))) (hpin i j l)

  obtain ⟨G, hGmul, -⟩ :=
    WeierstrassProjModel.exists_relativeGroupLaw_mul_eq_one_eq_zeroSect_of_addMorphism_sixU_pin
      (R := R) V m hm_over hmpin

  obtain ⟨ev, hev⟩ :=
    WeierstrassProjModel.exists_isPointsEval_of_addMorphism_sixU_pin (R := R) V hΔ m hmpin G
      (fun t x y => hGmul t x y)
  exact ⟨hbc, G, ev, hev⟩

end S_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain
end P2MW
export P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain (solution)
