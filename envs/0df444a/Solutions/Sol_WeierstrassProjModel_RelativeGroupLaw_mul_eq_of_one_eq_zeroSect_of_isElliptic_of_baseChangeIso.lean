-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/06b673ae-8e81-5589-a091-2b1d6a1aeeca

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassProjModel_isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_algebraTower_of_mul_eq
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

set_option maxHeartbeats 4800000 in
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in
theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G₀ G₁ : RelativeGroupLaw R (projModelStrCR V))
    (hone₀ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        (G₀.one t).1 = t ≫ (kwZeroSect R V.toAffine).1)
    (hone₁ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        (G₁.one t).1 = t ≫ (kwZeroSect R V.toAffine).1) :
    ∀ (F : Type u) [Field F] [Algebra R F],
      ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V),
        G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q
          = G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q := by

  haveI : IsSeparated (projModelStrCR V) :=
    (WeierstrassProjModel.projModelStrCR_isProper V).toIsSeparated
  intro F _ _

  let K := AlgebraicClosure F

  obtain ⟨hP, hI, hR⟩ :=
    WeierstrassProjModel.isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso
      V K (hbc K)

  have honeK : G₀.one (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      = G₁.one (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    Subtype.ext ((hone₀ _).trans (hone₁ _).symm)
  have hC2 :=
    @WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isAlgClosed
      R _ _ (projModelStrCR V) K _ _ _ hP hI hR G₀ G₁ honeK

  exact WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_algebraTower_of_mul_eq
    F K G₀ G₁ hC2

end S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso (solution)
