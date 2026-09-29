-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_comp_projMap_eq_projMap_comp_isPullback_of_isCoefficientHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/072dd0df-03b0-5a8d-9aee-ee0686d7d84a

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_comp_projMap_eq_projMap_comp_isPullback_of_isCoefficientHom

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T T' : Type} [CommRing T] [CommRing T'] (f : T →+* T')
    (W₁ W₂ : WeierstrassCurve T)
    (u : projModelCR W₁.toProjective ⟶ projModelCR W₂.toProjective)
    (hu : u ≫ projModelStrCR W₂.toProjective = projModelStrCR W₁.toProjective)
    (φ₁ : projModelGradingCR W₁.toProjective →+*ᵍ projModelGradingCR (W₁.map f).toProjective)
    (hφ₁ : HomogeneousIdeal.irrelevant (projModelGradingCR (W₁.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₁.toProjective)).map φ₁)
    (hcoef₁ : IsCoefficientHom W₁.toProjective f φ₁)
    (φ₂ : projModelGradingCR W₂.toProjective →+*ᵍ projModelGradingCR (W₂.map f).toProjective)
    (hφ₂ : HomogeneousIdeal.irrelevant (projModelGradingCR (W₂.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₂.toProjective)).map φ₂)
    (hcoef₂ : IsCoefficientHom W₂.toProjective f φ₂) :
    ∃ u' : projModelCR (W₁.map f).toProjective ⟶ projModelCR (W₂.map f).toProjective,
      u' ≫ projModelStrCR (W₂.map f).toProjective = projModelStrCR (W₁.map f).toProjective ∧
      u' ≫ Proj.map φ₂ hφ₂ = Proj.map φ₁ hφ₁ ≫ u ∧
      IsPullback u' (Proj.map φ₁ hφ₁) (Proj.map φ₂ hφ₂) u ∧
      ∀ u'' : projModelCR (W₁.map f).toProjective ⟶ projModelCR (W₂.map f).toProjective,
        u'' ≫ projModelStrCR (W₂.map f).toProjective = projModelStrCR (W₁.map f).toProjective →
        u'' ≫ Proj.map φ₂ hφ₂ = Proj.map φ₁ hφ₁ ≫ u → u'' = u' := by
  have hpb₁ := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W₁.toProjective f φ₁ hφ₁ hcoef₁
  have hpb₂ := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W₂.toProjective f φ₂ hφ₂ hcoef₂
  have w : (Proj.map φ₁ hφ₁ ≫ u) ≫ projModelStrCR W₂.toProjective =
      projModelStrCR (W₁.map f).toProjective ≫ Spec.map (CommRingCat.ofHom f) := by
    rw [Category.assoc, hu]; exact hpb₁.w
  refine ⟨hpb₂.lift (Proj.map φ₁ hφ₁ ≫ u) (projModelStrCR (W₁.map f).toProjective) w,
    hpb₂.lift_snd _ _ w, hpb₂.lift_fst _ _ w, ?_, ?_⟩
  · refine IsPullback.of_right ?_ (hpb₂.lift_fst _ _ w) hpb₂.flip
    rw [hpb₂.lift_snd _ _ w, hu]
    exact hpb₁.flip
  · intro u'' hu''s hu''f
    exact hpb₂.hom_ext (by rw [hu''f, hpb₂.lift_fst]) (by rw [hu''s, hpb₂.lift_snd])

end S_WeierstrassCurve_DrinfeldGlobal_exists_comp_projMap_eq_projMap_comp_isPullback_of_isCoefficientHom
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_comp_projMap_eq_projMap_comp_isPullback_of_isCoefficientHom (solution)
