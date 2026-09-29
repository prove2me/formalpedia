-- Prove2me | solution 1 for WeierstrassProjModel.isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/be6414b0-133f-5f7a-aac0-90a82ee33f89

import Definitions.Def_WeierstrassCurve_ProjModel
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_kw_r0_isIntegral_pullbacks
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_projModel_isPullback_baseChange
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (F : Type u) [Field F] [Algebra R F]
    (hbc : Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R F)))
          ≅ projModelCR (V.baseChange F))) :
    IsProper (pullback.snd (projModelStrCR V)
        (Spec.map (CommRingCat.ofHom (algebraMap R F))))
    ∧ IsIntegral ↑(pullback (projModelStrCR V)
        (Spec.map (CommRingCat.ofHom (algebraMap R F))))
    ∧ IsReduced ↑(pullback
        (pullback.snd (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap R F))))
        (pullback.snd (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap R F))))) := by

  haveI : (V.baseChange F).IsElliptic :=
    show (WeierstrassCurve.map V (algebraMap R F)).IsElliptic from inferInstance
  have hsm : Smooth (projModelStrCR (V.baseChange F)) := by
    haveI := projModelStrCR_smoothOfRelativeDimension_one (V.baseChange F : WeierstrassCurve.Projective F)
    exact SmoothOfRelativeDimension.smooth (n := 1) (f := projModelStrCR (V.baseChange F))
  have hgi : GeometricallyIntegral (projModelStrCR (V.baseChange F)) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso (V.baseChange F)
      (fun K _ _ => projModel_pullback_iso_baseChange (V.baseChange F : WeierstrassCurve.Projective F) K)

  obtain ⟨hint, hint2, -⟩ := kw_r0_isIntegral_pullbacks (V.baseChange F) hsm hgi

  obtain ⟨α, hα⟩ := projModel_isPullback_baseChange V F
  haveI := projModelStrCR_isProper V
  refine ⟨inferInstance, ?_, ?_⟩
  · haveI := hint
    exact IsIntegral.of_isIso hα.isoPullback.hom
  · haveI := hint2
    have hsnd : pullback.snd (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap R F)))
          ≫ 𝟙 _ = hα.isoPullback.inv ≫ projModelStrCR (V.baseChange F) := by
      rw [Category.comp_id]
      exact hα.isoPullback_inv_snd.symm
    exact isReduced_of_isOpenImmersion
      (pullback.map _ _ (projModelStrCR (V.baseChange F)) (projModelStrCR (V.baseChange F))
        hα.isoPullback.inv hα.isoPullback.inv (𝟙 _) hsnd hsnd)

end S_WeierstrassProjModel_isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso
end P2MW
export P2MW.S_WeierstrassProjModel_isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso (solution)
