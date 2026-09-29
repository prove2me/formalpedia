-- Prove2me | solution 1 for WeierstrassProjModel.outerCompat_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4a2cdb1b-5416-565b-922c-043d4525b02a

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero
import Theorems.Thm_WeierstrassProjModel_sixU_toE_over
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_outerCompat_of_smooth

set_option Elab.async false

section MEGA_prelude_occ_lean

end MEGA_prelude_occ_lean

section MEGA_DensityKit_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrAdd_c₂₁ kw_lrAdd_c₁₂ kw_lrAdd_starX kw_lrAdd_starY kw_lrAdd_starZ kw_lrAdd_X kw_lrAdd_Y kw_lrAdd_Z kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU KwLRSixUCoverage kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap KwLRPerChartCompat kw_lrPerChart_toE kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrOuter_toE KwLROuterCompat kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over"
namespace Density
p2m_open "WeierstrassProjModel"

universe u

section Integral

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {X : Scheme.{u}}

theorem isIntegral_of_smooth_of_geometricallyIntegral (q : X ⟶ Spec (CommRingCat.of R))
    [Smooth q] [GeometricallyIntegral q] : IsIntegral X :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian q

theorem isIntegral_pullback₂ (q : X ⟶ Spec (CommRingCat.of R))
    [Smooth q] [GeometricallyIntegral q] : IsIntegral ↑(pullback q q) := by
  haveI : IsIntegral X := isIntegral_of_smooth_of_geometricallyIntegral q
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : GeometricallyIntegral (pullback.fst q q) :=
    MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral q›
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst q q)

end Integral

section GenericPoint

variable (X : Scheme.{u}) [IsIntegral X]

abbrev genericInclusion : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

theorem isDominant_genericInclusion : IsDominant (genericInclusion X) := by
  rw [isDominant_iff, DenseRange, Scheme.range_fromSpecStalk]
  refine Dense.mono (Set.singleton_subset_iff.mpr (specializes_refl _)) ?_
  exact dense_iff_closure_eq.mpr (genericPoint_spec X)

scoped instance isSchemeTheoreticallyDominant_genericInclusion :
    IsSchemeTheoreticallyDominant (genericInclusion X) := by
  haveI := isDominant_genericInclusion X
  exact IsSchemeTheoreticallyDominant.of_isDominant (genericInclusion X)

variable {X} {R : Type u} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R))

abbrev functionFieldAlgebra : Algebra R X.functionField :=
  (Spec.preimage (genericInclusion X ≫ q)).hom.toAlgebra

theorem genericInclusion_comp :
    letI := functionFieldAlgebra q
    genericInclusion X ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) := by
  letI := functionFieldAlgebra q
  show genericInclusion X ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R X.functionField))
  rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]

end GenericPoint

end WeierstrassProjModel.Density
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end MEGA_DensityKit_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section MEGA_KwLROuterGlue_lean

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrAdd_c₂₁ kw_lrAdd_c₁₂ kw_lrAdd_starX kw_lrAdd_starY kw_lrAdd_starZ kw_lrAdd_X kw_lrAdd_Y kw_lrAdd_Z kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU KwLRSixUCoverage kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap KwLRPerChartCompat kw_lrPerChart_toE kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrOuter_toE KwLROuterCompat kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective

theorem kw_lrOuter_toE_apply (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) (i j : Fin 3) :
    kw_lrOuter_toE W hcov hcompat (i, j)
      = (kwProjPullbackChartIsoCR R W.toProjective i j).hom
          ≫ kw_lrPerChart_toE W hcov hcompat i j := rfl

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"
end MEGA_KwLROuterGlue_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section MEGA_ToEShim

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel"
open scoped TensorProduct

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrAdd_c₂₁ kw_lrAdd_c₁₂ kw_lrAdd_starX kw_lrAdd_starY kw_lrAdd_starZ kw_lrAdd_X kw_lrAdd_Y kw_lrAdd_Z kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU KwLRSixUCoverage kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap KwLRPerChartCompat kw_lrPerChart_toE kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrOuter_toE KwLROuterCompat kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem kw_lrSixU_toE_over (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) :
    kw_lrSixU_toE W i j l ≫ projModelStrCR W.toProjective
      = kw_lrSixU_locMap W i j l
          ≫ Spec.map (CommRingCat.ofHom (algebraMap R
              (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (MvPolynomial.X i : MvPolynomial (Fin 3) R))
                ⊗[R] HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (MvPolynomial.X j : MvPolynomial (Fin 3) R))))) :=
  WeierstrassProjModel.sixU_toE_over W i j l

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end MEGA_ToEShim
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section MEGA_KwLRAddMorphismOver_lean

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrAdd_c₂₁ kw_lrAdd_c₁₂ kw_lrAdd_starX kw_lrAdd_starY kw_lrAdd_starZ kw_lrAdd_X kw_lrAdd_Y kw_lrAdd_Z kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU KwLRSixUCoverage kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap KwLRPerChartCompat kw_lrPerChart_toE kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrOuter_toE KwLROuterCompat kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective

section RingHelpers

variable (i j k : Fin 3)

theorem kw_lrSixU_cover_openCover_f
    (h : Ideal.span (Set.range (kw_lrSixU W i j)) = ⊤) (l : Fin 3 ⊕ Fin 3) :
    (kw_lrSixU_cover W i j h).openCover.f l = kw_lrSixU_locMap W i j l := rfl

theorem kw_lrAddMorphismOver_coverL_f_comp :
    (projModelAffineOpenCoverCR R W.toProjective).openCover.f i
        ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 i))) :=
  kw_pbac_awayι_comp_projModelStrCR R W.toProjective i

theorem kw_lrAddMorphismOver_chartIso_hom_base :
    (kwProjPullbackChartIsoCR R W.toProjective i j).hom
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j))))
      = pullback.fst ((projModelAffineOpenCoverCR R W.toProjective).openCover.f i
            ≫ projModelStrCR W.toProjective)
          ((projModelAffineOpenCoverCR R W.toProjective).openCover.f j
            ≫ projModelStrCR W.toProjective)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 i))) := by
  refine .trans (Category.assoc
      (pullback.congrHom (kw_pbac_awayι_comp_projModelStrCR R W.toProjective i)
        (kw_pbac_awayι_comp_projModelStrCR R W.toProjective j)).hom
      (pullbackSpecIso R (𝒜 i) (𝒜 j)).hom _) ?_
  rw [pullbackSpecIso_hom_base, pullback.congrHom_hom,
    pullback.lift_fst_assoc, Category.comp_id]
  rfl

end RingHelpers
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

theorem kw_lrPerChart_toE_over (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) (i j : Fin 3) :
    kw_lrPerChart_toE W hcov hcompat i j ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j)))) := by
  apply (kw_lrSixU_cover W i j (hcov i j)).openCover.hom_ext
  intro l
  rw [kw_lrPerChart_toE, Scheme.Cover.ι_glueMorphisms_assoc,
    kw_lrSixU_cover_openCover_f]
  exact kw_lrSixU_toE_over W i j l

theorem kw_lrOuter_toE_over (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) (ij : Fin 3 × Fin 3) :
    kw_lrOuter_toE W hcov hcompat ij ≫ projModelStrCR W.toProjective
      = (kwProjPullbackOpenCoverCR R W.toProjective).f ij
          ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective := by
  obtain ⟨i, j⟩ := ij
  refine .trans (.trans (Category.assoc _ _ _)
      (.trans (congrArg ((kwProjPullbackChartIsoCR R W.toProjective i j).hom ≫ ·)
          (kw_lrPerChart_toE_over W hcov hcompat i j))
        (kw_lrAddMorphismOver_chartIso_hom_base W i j))) ?_
  simp only [kwProjPullbackOpenCoverCR, Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_fst_assoc]
  exact ((Category.assoc _ _ _).trans
    (congrArg (pullback.fst _ _ ≫ ·) (kw_lrAddMorphismOver_coverL_f_comp W i))).symm

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"
end MEGA_KwLRAddMorphismOver_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section MEGA_KwLRAffinePtSetEquiv_lean

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial
open HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped WeierstrassCurve.Projective

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrAdd_c₂₁ kw_lrAdd_c₁₂ kw_lrAdd_starX kw_lrAdd_starY kw_lrAdd_starZ kw_lrAdd_X kw_lrAdd_Y kw_lrAdd_Z kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU KwLRSixUCoverage kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap KwLRPerChartCompat kw_lrPerChart_toE kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrOuter_toE KwLROuterCompat kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over"
p2m_open "WeierstrassProjModel"

p2m_open "WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel NeronModelInfra"

attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover
set_option quotPrecheck false in
local notation "gen" => kw_lrChart_gen W
set_option quotPrecheck false in
local notation "dehom" => kw_lrChart_dehom W
set_option quotPrecheck false in
local notation "t_F" => kw_lrAptb_tF (R := R) F
set_option quotPrecheck false in
local notation "awayι₃" i => Proj.awayι (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R)) (kw_pbac_mk_X_mem_one_CR R W.toProjective i) one_pos

set_option quotPrecheck false in
local notation "W_F" => kw_lrApt_WF W F

theorem kw_lrApt_coverE_f_comp_π (i : Fin 3) :
    (coverE).f i ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 i))) :=
  kw_pbac_awayι_comp_projModelStrCR R W.toProjective i

section ChartClassification

theorem kw_lrApt_gen_self (i : Fin 3) : gen i i = 1 := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [kw_lrChart_gen_val, HomogeneousLocalization.val_one]
  exact Localization.mk_self
    (⟨mk₃ (X i : MvPolynomial (Fin 3) R), 1, pow_one _⟩ : Submonoid.powers _)

theorem kw_lrApt_chartEval_self (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    kw_lrApt_chartEval W F i ψ i = 1 := by
  unfold kw_lrApt_chartEval
  rw [kw_lrApt_gen_self W i, map_one]

theorem kw_lrApt_aeval_chartEval (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    (aeval (kw_lrApt_chartEval W F i ψ) : MvPolynomial (Fin 3) R →ₐ[R] F)
      = ψ.comp (dehom i) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  show aeval _ (X m) = ψ (aeval _ (X m))
  rw [aeval_X, aeval_X]; rfl

theorem kw_lrApt_dehom_surjective (i : Fin 3) :
    Function.Surjective (kw_lrChart_dehom W i) := fun x => by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (projModelGradingCR W.toProjective) (kw_lrChart_mkX_mem_one W i) x
  have ha' : a ∈ projModelGradingCR W.toProjective n := by simpa using ha
  obtain ⟨p, hpmem, hpeq⟩ := (mem_quotGradingSubmodule_iff _ _).mp ha'
  refine ⟨p, ?_⟩
  rw [kw_lrChart_dehom_isHomogeneous W i n p ((mem_homogeneousSubmodule _ _).mp hpmem)]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, hpeq]

theorem kw_lrApt_chartEval_injective (i : Fin 3) :
    Function.Injective (kw_lrApt_chartEval W F i) := fun ψ ψ' h => by
  have hd : ψ.comp (dehom i) = ψ'.comp (dehom i) := by
    rw [← kw_lrApt_aeval_chartEval, ← kw_lrApt_aeval_chartEval, h]
  exact AlgHom.ext fun x => by
    obtain ⟨p, rfl⟩ := kw_lrApt_dehom_surjective W i x
    exact AlgHom.congr_fun hd p

end ChartClassification
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section ChartFactorization

theorem kw_lrApt_factor_of_range (φ : SchemeHomOver (t_F) π) (i : Fin 3)
    (hrange : Set.range φ.1 ⊆ Set.range (awayι₃ i)) :
    ∃ ψ : (𝒜 i) →ₐ[R] F,
      φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (coverE).f i := by
  let g : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (𝒜 i)) :=
    IsOpenImmersion.lift (awayι₃ i) φ.1 hrange
  have hgfac : g ≫ (coverE).f i = φ.1 := IsOpenImmersion.lift_fac (awayι₃ i) φ.1 hrange
  let ρ : CommRingCat.of (𝒜 i) ⟶ CommRingCat.of F := Spec.preimage g
  have hρ : Spec.map ρ = g := Spec.map_preimage g
  have hspec : Spec.map (CommRingCat.ofHom (ρ.hom.comp (algebraMap R (𝒜 i))))
      = Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hρ,
      ← kw_lrApt_coverE_f_comp_π W i]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (projModelStrCR W.toProjective)) hgfac).trans φ.2)
  have hcomm : ρ.hom.comp (algebraMap R (𝒜 i)) = algebraMap R F :=
    CommRingCat.hom_ext_iff.mp (Spec.map_injective hspec)
  exact ⟨⟨ρ.hom, RingHom.congr_fun hcomm⟩,
    by rw [show (⟨ρ.hom, RingHom.congr_fun hcomm⟩ : (𝒜 i) →ₐ[R] F).toRingHom = ρ.hom from rfl,
        CommRingCat.ofHom_hom, hρ, hgfac]⟩

theorem kw_lrApt_schemeHom_factor (φ : SchemeHomOver (t_F) π) :
    ∃ (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F),
      φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (coverE).f i := by
  let pt : ↑(Spec (CommRingCat.of F)) := default
  let i := (coverE).idx (φ.1.base pt)
  have hrange : Set.range φ.1 ⊆ Set.range (awayι₃ i) := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q pt]
    exact (coverE).covers (φ.1.base pt)
  exact ⟨i, kw_lrApt_factor_of_range W F φ i hrange⟩

noncomputable def kw_lrApt_chartIdx (φ : SchemeHomOver (t_F) π) : Fin 3 :=
  (kw_lrApt_schemeHom_factor W F φ).choose

noncomputable def kw_lrApt_chartHom (φ : SchemeHomOver (t_F) π) :
    (𝒜 (kw_lrApt_chartIdx W F φ)) →ₐ[R] F :=
  (kw_lrApt_schemeHom_factor W F φ).choose_spec.choose

theorem kw_lrApt_chartHom_fac (φ : SchemeHomOver (t_F) π) :
    φ.1 = Spec.map (CommRingCat.ofHom (kw_lrApt_chartHom W F φ).toRingHom)
            ≫ (coverE).f (kw_lrApt_chartIdx W F φ) :=
  (kw_lrApt_schemeHom_factor W F φ).choose_spec.choose_spec

theorem kw_lrApt_gen_eq_awayMk (i m : Fin 3) :
    gen i m = HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
      (kw_lrChart_mkX_mem_one W i) 1 (mk₃ (X m : MvPolynomial (Fin 3) R))
      (kw_lrChart_mk_mem_of_isHomogeneous W 1 (X m) (isHomogeneous_X R m)) := by
  have h := kw_lrChart_dehom_isHomogeneous W i 1 (X m) (isHomogeneous_X R m)
  rw [kw_lrChart_dehom, aeval_X] at h; exact h

theorem kw_lrApt_awayMap_gen_identity (i j m : Fin 3) :
    HomogeneousLocalization.awayMap (projModelGradingCR W.toProjective)
        (kw_lrChart_mkX_mem_one W i)
        (mul_comm (mk₃ (X i : MvPolynomial (Fin 3) R)) (mk₃ (X j : _))) (gen j m)
      * HomogeneousLocalization.awayMap (projModelGradingCR W.toProjective)
        (kw_lrChart_mkX_mem_one W j) rfl (gen i j)
      = HomogeneousLocalization.awayMap (projModelGradingCR W.toProjective)
        (kw_lrChart_mkX_mem_one W j) rfl (gen i m) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul,
    kw_lrApt_gen_eq_awayMk W j m, kw_lrApt_gen_eq_awayMk W i j, kw_lrApt_gen_eq_awayMk W i m,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

theorem kw_lrApt_chartEval_compat {i j : Fin 3}
    {ψᵢ : (𝒜 i) →ₐ[R] F} {ψⱼ : (𝒜 j) →ₐ[R] F}
    (hfac_i : ∃ φ : SchemeHomOver (t_F) π,
      φ.1 = Spec.map (CommRingCat.ofHom ψᵢ.toRingHom) ≫ (coverE).f i ∧
      φ.1 = Spec.map (CommRingCat.ofHom ψⱼ.toRingHom) ≫ (coverE).f j) :
    (⟦kw_lrApt_chartEval W F i ψᵢ⟧ : Projective.PointClass F)
      = ⟦kw_lrApt_chartEval W F j ψⱼ⟧ := by
  obtain ⟨φ, hφi, hφj⟩ := hfac_i
  have hmem : mk₃ (X i : MvPolynomial (Fin 3) R) * mk₃ (X j : _)
      ∈ projModelGradingCR W.toProjective (1 + 1) :=
    SetLike.mul_mem_graded (kw_lrChart_mkX_mem_one W i) (kw_lrChart_mkX_mem_one W j)
  have hrange : Set.range φ.1 ⊆ Set.range (Proj.awayι (projModelGradingCR W.toProjective)
      (mk₃ (X i : MvPolynomial (Fin 3) R) * mk₃ (X j : _)) hmem two_pos) := by
    have hcap : (Proj.awayι _ _ hmem two_pos).opensRange
        = (awayι₃ i).opensRange ⊓ (awayι₃ j).opensRange := by
      rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.opensRange_awayι,
        ← Proj.basicOpen_mul]
    intro x hx
    rw [← Scheme.Hom.coe_opensRange, hcap]
    exact ⟨(Set.range_comp_subset_range _ _) (hφi ▸ hx),
      (Set.range_comp_subset_range _ _) (hφj ▸ hx)⟩
  let g := IsOpenImmersion.lift _ φ.1 hrange
  have hgfac : g ≫ _ = φ.1 := IsOpenImmersion.lift_fac _ _ hrange
  let χ := Spec.preimage g
  have hχ : Spec.map χ = g := Spec.map_preimage g
  have hcompᵢ : χ.hom.comp (HomogeneousLocalization.awayMap
        (projModelGradingCR W.toProjective) (kw_lrChart_mkX_mem_one W j) rfl)
      = ψᵢ.toRingHom := by
    have hs : Spec.map (CommRingCat.ofHom ψᵢ.toRingHom)
        = Spec.map (CommRingCat.ofHom (χ.hom.comp (HomogeneousLocalization.awayMap _
            (kw_lrChart_mkX_mem_one W j) rfl))) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hχ,
        ← cancel_mono (awayι₃ i), Category.assoc, Proj.SpecMap_awayMap_awayι, hgfac, hφi]; rfl
    exact (CommRingCat.hom_ext_iff.mp (Spec.map_injective hs)).symm
  have hcompⱼ : χ.hom.comp (HomogeneousLocalization.awayMap
        (projModelGradingCR W.toProjective) (kw_lrChart_mkX_mem_one W i) (mul_comm _ _))
      = ψⱼ.toRingHom := by
    have hs : Spec.map (CommRingCat.ofHom ψⱼ.toRingHom)
        = Spec.map (CommRingCat.ofHom (χ.hom.comp (HomogeneousLocalization.awayMap _
            (kw_lrChart_mkX_mem_one W i) (mul_comm _ _)))) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hχ,
        ← cancel_mono (awayι₃ j), Category.assoc, Proj.SpecMap_awayMap_awayι, hgfac, hφj]; rfl
    exact (CommRingCat.hom_ext_iff.mp (Spec.map_injective hs)).symm
  have hχᵢ : ∀ a, χ.hom (HomogeneousLocalization.awayMap (projModelGradingCR W.toProjective)
      (kw_lrChart_mkX_mem_one W j) rfl a) = ψᵢ a :=
    fun a => RingHom.congr_fun hcompᵢ a
  have hχⱼ : ∀ a, χ.hom (HomogeneousLocalization.awayMap (projModelGradingCR W.toProjective)
      (kw_lrChart_mkX_mem_one W i) (mul_comm _ _) a) = ψⱼ a :=
    fun a => RingHom.congr_fun hcompⱼ a
  have hprop : ∀ m, kw_lrApt_chartEval W F j ψⱼ m * kw_lrApt_chartEval W F i ψᵢ j
      = kw_lrApt_chartEval W F i ψᵢ m := fun m => by
    have hid := congrArg χ.hom (kw_lrApt_awayMap_gen_identity W i j m)
    rw [map_mul, hχⱼ, hχᵢ, hχᵢ] at hid
    exact hid
  have hunit : IsUnit (kw_lrApt_chartEval W F i ψᵢ j) := by
    refine isUnit_iff_ne_zero.mpr fun hz => ?_
    have h := hprop i; rw [hz, mul_zero, kw_lrApt_chartEval_self] at h
    exact one_ne_zero h.symm
  rw [show kw_lrApt_chartEval W F i ψᵢ
      = (kw_lrApt_chartEval W F i ψᵢ j) • kw_lrApt_chartEval W F j ψⱼ
      from funext fun m => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, hprop m]]
  exact Projective.smul_eq _ hunit

end ChartFactorization
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section Forward

noncomputable def kw_lrApt_toVec (φ : SchemeHomOver (t_F) π) : Fin 3 → F :=
  kw_lrApt_chartEval W F (kw_lrApt_chartIdx W F φ) (kw_lrApt_chartHom W F φ)

noncomputable def kw_lrApt_toPointClass (φ : SchemeHomOver (t_F) π) :
    Projective.PointClass F :=
  ⟦kw_lrApt_toVec W F φ⟧

theorem kw_lrApt_toPointClass_eq_of_fac (φ : SchemeHomOver (t_F) π) (i : Fin 3)
    (ψ : (𝒜 i) →ₐ[R] F)
    (hfac : φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (coverE).f i) :
    kw_lrApt_toPointClass W F φ = ⟦kw_lrApt_chartEval W F i ψ⟧ := by
  exact kw_lrApt_chartEval_compat W F
    ⟨φ, kw_lrApt_chartHom_fac W F φ, hfac⟩

end Forward
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section Nonsingular

variable {F}

end Nonsingular
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section Inverse

theorem kw_lrApt_eq_of_equiv_of_apply_eq_one {P Q : Fin 3 → F} {i : Fin 3}
    (heq : P ≈ Q) (hPi : P i = 1) (hQi : Q i = 1) : P = Q := by
  obtain ⟨u, hu⟩ := heq
  change u • Q = P at hu
  have hui : u = 1 := by
    refine Units.ext ?_
    have h := congr_fun hu i
    rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, hQi, mul_one] at h
    exact h.trans hPi
  rw [← hu, hui, one_smul]

theorem kw_lrApt_range_subset_of_gen_ne_zero {j : Fin 3} (ψ : (𝒜 j) →ₐ[R] F)
    (i : Fin 3) (hij : ψ (gen j i) ≠ 0) :
    Set.range (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (awayι₃ j))
      ⊆ Set.range (awayι₃ i) := by
  have hxrfl : mk₃ (X j : MvPolynomial (Fin 3) R) * mk₃ (X i : MvPolynomial (Fin 3) R)
      = mk₃ (X j : MvPolynomial (Fin 3) R) * mk₃ (X i : MvPolynomial (Fin 3) R) := rfl
  letI := (awayMap (projModelGradingCR W.toProjective)
    (kw_lrChart_mkX_mem_one W i) hxrfl).toAlgebra
  haveI hloc := Away.isLocalization_mul
    (kw_lrChart_mkX_mem_one W j) (kw_lrChart_mkX_mem_one W i) hxrfl one_ne_zero
  have helem : Away.isLocalizationElem
      (kw_lrChart_mkX_mem_one W j) (kw_lrChart_mkX_mem_one W i) = gen j i := by
    rw [kw_lrApt_gen_eq_awayMk]; apply val_injective
    rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by push_cast; ring⟩
  have hunit : IsUnit (ψ.toRingHom (Away.isLocalizationElem
      (kw_lrChart_mkX_mem_one W j) (kw_lrChart_mkX_mem_one W i))) := by
    rw [helem]; exact isUnit_iff_ne_zero.mpr hij
  let χ := IsLocalization.Away.lift (S := Away (projModelGradingCR W.toProjective)
    (mk₃ (X j : MvPolynomial (Fin 3) R) * mk₃ (X i : MvPolynomial (Fin 3) R)))
    (Away.isLocalizationElem (kw_lrChart_mkX_mem_one W j) (kw_lrChart_mkX_mem_one W i)) hunit
  have hfac : ψ.toRingHom = χ.comp (awayMap (projModelGradingCR W.toProjective)
      (kw_lrChart_mkX_mem_one W i) hxrfl) := by
    ext a; symm
    show χ (algebraMap (𝒜 j) _ a) = ψ.toRingHom a
    unfold χ; rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hrefac : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (awayι₃ j)
      = Spec.map (CommRingCat.ofHom
          (χ.comp (awayMap _ (kw_lrChart_mkX_mem_one W j) (mul_comm _ _))))
        ≫ (awayι₃ i) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      Proj.SpecMap_awayMap_awayι,
      ← Proj.SpecMap_awayMap_awayι (g_deg := kw_lrChart_mkX_mem_one W i) (hx := hxrfl),
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hfac]
  rw [hrefac]
  exact fun x hx => Set.range_comp_subset_range _ _ hx

theorem kw_lrApt_toPointClass_injective :
    Function.Injective (kw_lrApt_toPointClass W F) := by
  intro φ φ' h
  set i := kw_lrApt_chartIdx W F φ with hi
  set ψ := kw_lrApt_chartHom W F φ with hψ
  have hφfac := kw_lrApt_chartHom_fac W F φ
  obtain ⟨j, ψ', hφ'fac⟩ := kw_lrApt_schemeHom_factor W F φ'
  have hprop : (⟦kw_lrApt_chartEval W F i ψ⟧ : Projective.PointClass F)
      = ⟦kw_lrApt_chartEval W F j ψ'⟧ :=
    (kw_lrApt_toPointClass_eq_of_fac W F φ i ψ hφfac).symm.trans
      (h.trans (kw_lrApt_toPointClass_eq_of_fac W F φ' j ψ' hφ'fac))
  have hψ'i : ψ' (gen j i) ≠ 0 := by
    intro hzero
    obtain ⟨u, hu⟩ := Quotient.eq.mp hprop
    change u • kw_lrApt_chartEval W F j ψ' = kw_lrApt_chartEval W F i ψ at hu
    have h1 := congr_fun hu i
    rw [Pi.smul_apply, show kw_lrApt_chartEval W F j ψ' i = ψ' (gen j i) from rfl,
      hzero, smul_zero, kw_lrApt_chartEval_self] at h1
    exact one_ne_zero h1.symm
  have hrange : Set.range φ'.1 ⊆ Set.range (awayι₃ i) := by
    rw [hφ'fac]; exact kw_lrApt_range_subset_of_gen_ne_zero W F ψ' i hψ'i
  obtain ⟨ψ'', hφ'fac_i⟩ := kw_lrApt_factor_of_range W F φ' i hrange
  have heveq : kw_lrApt_chartEval W F i ψ = kw_lrApt_chartEval W F i ψ'' :=
    kw_lrApt_eq_of_equiv_of_apply_eq_one (F := F)
      (Quotient.eq.mp
        (hprop.trans (kw_lrApt_chartEval_compat W F ⟨φ', hφ'fac, hφ'fac_i⟩)))
      (kw_lrApt_chartEval_self W F i ψ) (kw_lrApt_chartEval_self W F i ψ'')
  have hψeq : ψ = ψ'' := kw_lrApt_chartEval_injective W F i heveq
  exact Subtype.ext (hφfac.trans (hψeq ▸ hφ'fac_i).symm)

end Inverse
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section Assembly

variable (hΔ : algebraMap R F W.Δ ≠ 0)

end Assembly
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"
end MEGA_KwLRAffinePtSetEquiv_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section MEGA_DensityCompat_lean

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
open MvPolynomial HomogeneousLocalization WeierstrassCurve
open scoped TensorProduct

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrAdd_c₂₁ kw_lrAdd_c₁₂ kw_lrAdd_starX kw_lrAdd_starY kw_lrAdd_starZ kw_lrAdd_X kw_lrAdd_Y kw_lrAdd_Z kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU KwLRSixUCoverage kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap KwLRPerChartCompat kw_lrPerChart_toE kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrOuter_toE KwLROuterCompat kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective

section Overlap

variable (i j : Fin 3) (l l' : Fin 3 ⊕ Fin 3)

scoped instance kw_lrDcp_locMap_isOpenImmersion : IsOpenImmersion (kw_lrSixU_locMap W i j l) := by
  unfold kw_lrSixU_locMap
  infer_instance

abbrev kw_lrDcp_V : Scheme.{u} :=
  pullback (kw_lrSixU_locMap W i j l) (kw_lrSixU_locMap W i j l')

def kw_lrDcp_ιV : kw_lrDcp_V W i j l l' ⟶ pullback π π :=
  pullback.fst (kw_lrSixU_locMap W i j l) (kw_lrSixU_locMap W i j l')
    ≫ kw_lrSixU_locMap W i j l
    ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv
    ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j)

scoped instance kw_lrDcp_ιV_isOpenImmersion : IsOpenImmersion (kw_lrDcp_ιV W i j l l') := by
  unfold kw_lrDcp_ιV
  infer_instance

end Overlap
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section LiftOver

variable (K : Type u) [Field K] [Algebra R K] (i j : Fin 3)

set_option quotPrecheck false in
local notation "t_K" => kw_lrAptb_tF (R := R) K

theorem kw_lrDcp_liftToE_over (ψᵢ : (𝒜 i) →ₐ[R] K) (ψⱼ : (𝒜 j) →ₐ[R] K) (l : Fin 3 ⊕ Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l))) :
    (Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.lift (kw_lrSixU W i j l)
          (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
        ≫ kw_lrSixU_toE W i j l) ≫ π
      = t_K := by
  have hring : ((IsLocalization.Away.lift (kw_lrSixU W i j l)
        (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu).comp
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (kw_lrSixU W i j l)))).comp
        (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j)))
      = algebraMap R K := by
    rw [IsLocalization.Away.lift_comp]
    exact (Algebra.TensorProduct.productMap ψᵢ ψⱼ).comp_algebraMap
  rw [Category.assoc, kw_lrSixU_toE_over]
  show Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ((𝒜 i) ⊗[R] (𝒜 j))
      (Localization.Away (kw_lrSixU W i j l)))) ≫ _
    = Spec.map (CommRingCat.ofHom (algebraMap R K))
  rw [← hring]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end LiftOver
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

def KwLRSixUClassEqAddMap : Prop :=
  ∀ (K : Type u) [Field K] [Algebra R K] (_hΔK : algebraMap R K W.Δ ≠ 0) (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] K) (ψⱼ : (𝒜 j) →ₐ[R] K) (l : Fin 3 ⊕ Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l))),
    kw_lrApt_toPointClass W K
        ⟨Spec.map (CommRingCat.ofHom
            (IsLocalization.Away.lift (kw_lrSixU W i j l)
              (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrSixU_toE W i j l,
         kw_lrDcp_liftToE_over W K i j ψᵢ ψⱼ l hu⟩
      = (kw_lrApt_WF W K).addMap ⟦kw_lrApt_chartEval W K i ψᵢ⟧ ⟦kw_lrApt_chartEval W K j ψⱼ⟧

section Compat

variable [IsDomain R] [IsNoetherianRing R]

end Compat
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end MEGA_DensityCompat_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section MEGA_KwLRAffinePtAddEquivDischargeCore_lean

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option Elab.async false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial
open HomogeneousLocalization

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrAdd_c₂₁ kw_lrAdd_c₁₂ kw_lrAdd_starX kw_lrAdd_starY kw_lrAdd_starZ kw_lrAdd_X kw_lrAdd_Y kw_lrAdd_Z kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU KwLRSixUCoverage kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap KwLRPerChartCompat kw_lrPerChart_toE kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrOuter_toE KwLROuterCompat kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over"
p2m_open "WeierstrassProjModel"

p2m_open "WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel NeronModelInfra"

attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "W_F" => kw_lrApt_WF W F
set_option quotPrecheck false in
local notation "t_F" => kw_lrAptb_tF (R := R) F
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective

section Coeff

end Coeff
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section Check1

local macro "simp_check1" : tactic =>
  `(tactic| simp only [kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z, kw_lrAdd_starX,
      kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₁₂, kw_lrAdd_c₂₁,
      Projective.addX, Projective.addY, Projective.addZ, Projective.negAddY, Projective.negY,
      kw_lrApt_WF_a₁, kw_lrApt_WF_a₂, kw_lrApt_WF_a₃, kw_lrApt_WF_a₄, kw_lrApt_WF_a₆,
      map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, aeval_X, aeval_C,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one])

end Check1
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section Check2b

end Check2b
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section MapOne

set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover
set_option quotPrecheck false in
local notation "𝒜1" => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X 1 : MvPolynomial (Fin 3) R))

variable (hΔ : algebraMap R F W.Δ ≠ 0)

end MapOne
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section MapMulRaw

open scoped TensorProduct WeierstrassCurve.Projective

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover
set_option quotPrecheck false in
local notation "gen" => kw_lrChart_gen W

variable (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W)
  (houter : KwLROuterCompat W) (hΔ : algebraMap R F W.Δ ≠ 0)

section P2Helpers

variable (i j : Fin 3)

theorem kw_lrApt_chartIso_inv_fst :
    (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ pullback.fst _ _
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j))) := by
  simp only [kwProjPullbackChartIsoCR, Iso.trans_inv, Category.assoc]
  rw [pullback.congrHom_inv]
  erw [pullback.lift_fst]
  rw [Category.comp_id]
  exact pullbackSpecIso_inv_fst R (𝒜 i) (𝒜 j)

theorem kw_lrApt_chartIso_inv_snd :
    (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ pullback.snd _ _
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R) (A := 𝒜 i) (B := 𝒜 j)).toRingHom) := by
  simp only [kwProjPullbackChartIsoCR, Iso.trans_inv, Category.assoc]
  rw [pullback.congrHom_inv]
  erw [pullback.lift_snd]
  rw [Category.comp_id]
  exact pullbackSpecIso_inv_snd R (𝒜 i) (𝒜 j)

end P2Helpers
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

include hcov in

theorem kw_lrApt_exists_sixU_ne_zero (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) :
    ∃ l, (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l) ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hker : Set.range (kw_lrSixU W i j)
      ⊆ RingHom.ker (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom := by
    rintro _ ⟨l, rfl⟩; exact hall l
  have htop : (⊤ : Ideal ((𝒜 i) ⊗[R] (𝒜 j)))
      ≤ RingHom.ker (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom :=
    hcov i j ▸ Ideal.span_le.mpr hker
  have h1 : (Algebra.TensorProduct.productMap ψᵢ ψⱼ) 1 = 0 := htop Submodule.mem_top
  rw [map_one] at h1
  exact one_ne_zero h1

end MapMulRaw
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"
end MEGA_KwLRAffinePtAddEquivDischargeCore_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section MEGA_DensityOuterCompat_lean

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
open MvPolynomial HomogeneousLocalization WeierstrassCurve
open scoped TensorProduct

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrAdd_c₂₁ kw_lrAdd_c₁₂ kw_lrAdd_starX kw_lrAdd_starY kw_lrAdd_starZ kw_lrAdd_X kw_lrAdd_Y kw_lrAdd_Z kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU KwLRSixUCoverage kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap KwLRPerChartCompat kw_lrPerChart_toE kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrOuter_toE KwLROuterCompat kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "C9" => kwProjPullbackOpenCoverCR R W.toProjective
set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover

section Projections

variable (i j : Fin 3)

theorem kw_lrDoc_coverf_fst :
    (C9).f (i, j) ≫ pullback.fst π π
      = pullback.fst ((coverE).f i ≫ π) ((coverE).f j ≫ π) ≫ (coverE).f i := by
  simp only [kwProjPullbackOpenCoverCR, Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_fst]

theorem kw_lrDoc_coverf_snd :
    (C9).f (i, j) ≫ pullback.snd π π
      = pullback.snd ((coverE).f i ≫ π) ((coverE).f j ≫ π) ≫ (coverE).f j := by
  simp only [kwProjPullbackOpenCoverCR, Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_snd]

end Projections
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section Eval

variable (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W)
variable (K : Type u) [Field K] [Algebra R K] (i j : Fin 3)

set_option quotPrecheck false in
local notation "t_K" => kw_lrAptb_tF (R := R) K

theorem kw_lrDoc_perChart_factor
    (ψᵢ : (𝒜 i) →ₐ[R] K) (ψⱼ : (𝒜 j) →ₐ[R] K) (l : Fin 3 ⊕ Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l))) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
        ≫ kw_lrPerChart_toE W hcov hcompat i j
      = Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift (kw_lrSixU W i j l)
            (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrSixU_toE W i j l := by
  have hfact : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
      = Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift (kw_lrSixU W i j l)
            (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ (kw_lrSixU_cover W i j (hcov i j)).openCover.f l := by
    rw [kw_lrSixU_cover_openCover_f, kw_lrSixU_locMap, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp]
  have hgl : (kw_lrSixU_cover W i j (hcov i j)).openCover.f l
        ≫ kw_lrPerChart_toE W hcov hcompat i j
      = kw_lrSixU_toE W i j l :=
    (kw_lrSixU_cover W i j (hcov i j)).openCover.ι_glueMorphisms
      (kw_lrSixU_toE W i j) (hcompat i j) l
  exact (congrArg (· ≫ kw_lrPerChart_toE W hcov hcompat i j) hfact).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hgl))

theorem kw_lrDoc_pr₂_over (a : Spec (CommRingCat.of K) ⟶ (C9).X (i, j))
    (ha : (a ≫ (C9).f (i, j) ≫ pullback.fst π π) ≫ π = t_K) :
    (a ≫ (C9).f (i, j) ≫ pullback.snd π π) ≫ π = t_K := by
  rw [← ha]
  simp only [Category.assoc, pullback.condition (f := π) (g := π)]

theorem kw_lrDoc_outer_over (a : Spec (CommRingCat.of K) ⟶ (C9).X (i, j))
    (ha : (a ≫ (C9).f (i, j) ≫ pullback.fst π π) ≫ π = t_K) :
    (a ≫ kw_lrOuter_toE W hcov hcompat (i, j)) ≫ π = t_K := by
  rw [← ha]
  simp only [Category.assoc, kw_lrOuter_toE_over]

theorem kw_lrDoc_eval (hΔK : algebraMap R K W.Δ ≠ 0) (hclass : KwLRSixUClassEqAddMap W)
    (a : Spec (CommRingCat.of K) ⟶ (C9).X (i, j))
    (ha : (a ≫ (C9).f (i, j) ≫ pullback.fst π π) ≫ π = t_K) :
    kw_lrApt_toPointClass W K ⟨_, kw_lrDoc_outer_over W hcov hcompat K i j a ha⟩
      = (kw_lrApt_WF W K).addMap
          (kw_lrApt_toPointClass W K ⟨_, ha⟩)
          (kw_lrApt_toPointClass W K ⟨_, kw_lrDoc_pr₂_over W K i j a ha⟩) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ((𝒜 i) ⊗[R] (𝒜 j)) →+* K,
      a ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).hom = Spec.map (CommRingCat.ofHom ρ) :=
    ⟨(Spec.preimage (a ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).hom)).hom,
      by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have ha' : a = Spec.map (CommRingCat.ofHom ρ)
      ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv := by
    rw [← hρ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hx : a ≫ (C9).f (i, j) ≫ pullback.fst π π
      = Spec.map (CommRingCat.ofHom (ρ.comp
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j))))
        ≫ (coverE).f i := by
    rw [kw_lrDoc_coverf_fst, ha', CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (Spec.map (CommRingCat.ofHom ρ) ≫ ·)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (coverE).f i)
        (kw_lrApt_chartIso_inv_fst W i j)))).trans (Category.assoc _ _ _).symm)
  have hy : a ≫ (C9).f (i, j) ≫ pullback.snd π π
      = Spec.map (CommRingCat.ofHom (ρ.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := 𝒜 i) (B := 𝒜 j)).toRingHom))
        ≫ (coverE).f j := by
    rw [kw_lrDoc_coverf_snd, ha', CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (Spec.map (CommRingCat.ofHom ρ) ≫ ·)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (coverE).f j)
        (kw_lrApt_chartIso_inv_snd W i j)))).trans (Category.assoc _ _ _).symm)
  have hρalg : ρ.comp (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j))) = algebraMap R K := by
    have h1 : Spec.map (CommRingCat.ofHom (ρ.comp (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j)))))
        = t_K := by
      have e1 : ρ.comp (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j)))
          = (ρ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j))).comp
              (algebraMap R (𝒜 i)) := by
        rw [RingHom.comp_assoc]
        exact congrArg ρ.comp
          (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := 𝒜 i) (B := 𝒜 j)).comp_algebraMap.symm
      rw [e1, CommRingCat.ofHom_comp, Spec.map_comp, ← ha, hx, Category.assoc]
      exact congrArg (Spec.map _ ≫ ·) (kw_lrAddMorphismOver_coverL_f_comp W i).symm
    simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  let ψ : ((𝒜 i) ⊗[R] (𝒜 j)) →ₐ[R] K := { ρ with commutes' := fun r => RingHom.congr_fun hρalg r }
  have hψρ : ψ.toRingHom = ρ := rfl
  have hψi : (ψ.comp Algebra.TensorProduct.includeLeft).toRingHom
      = ρ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j)) := rfl
  have hψj : ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom
      = ρ.comp (Algebra.TensorProduct.includeRight (R := R) (A := 𝒜 i) (B := 𝒜 j)).toRingHom :=
    rfl
  have hprod : Algebra.TensorProduct.productMap (ψ.comp Algebra.TensorProduct.includeLeft)
      ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight) = ψ := by
    refine Algebra.TensorProduct.ext' fun x y => ?_
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    show ψ (x ⊗ₜ 1) * ψ (1 ⊗ₜ y) = ψ (x ⊗ₜ y)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  obtain ⟨l, hl⟩ := kw_lrApt_exists_sixU_ne_zero W K hcov i j
    (ψ.comp Algebra.TensorProduct.includeLeft)
    ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight)
  have hu : IsUnit ((Algebra.TensorProduct.productMap (ψ.comp Algebra.TensorProduct.includeLeft)
      ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight)) (kw_lrSixU W i j l)) :=
    isUnit_iff_ne_zero.mpr hl
  have hfac := kw_lrDoc_perChart_factor W hcov hcompat K i j
    (ψ.comp Algebra.TensorProduct.includeLeft)
    ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight) l hu
  have hpr : (Algebra.TensorProduct.productMap (ψ.comp Algebra.TensorProduct.includeLeft)
      ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight)).toRingHom = ρ := by
    rw [hprod]
  have hout : a ≫ kw_lrOuter_toE W hcov hcompat (i, j)
      = Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift (kw_lrSixU W i j l)
            (g := (Algebra.TensorProduct.productMap (ψ.comp Algebra.TensorProduct.includeLeft)
              ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight)).toRingHom) hu))
        ≫ kw_lrSixU_toE W i j l := by
    rw [kw_lrOuter_toE_apply, ← Category.assoc, hρ]
    exact (congrArg (fun r => Spec.map (CommRingCat.ofHom r)
      ≫ kw_lrPerChart_toE W hcov hcompat i j) hpr).symm.trans hfac
  have hL : kw_lrApt_toPointClass W K ⟨_, kw_lrDoc_outer_over W hcov hcompat K i j a ha⟩
      = kw_lrApt_toPointClass W K ⟨_, kw_lrDcp_liftToE_over W K i j _ _ l hu⟩ :=
    congrArg (kw_lrApt_toPointClass W K) (Subtype.ext hout)
  rw [hL, hclass K hΔK i j _ _ l hu,
    kw_lrApt_toPointClass_eq_of_fac W K ⟨_, ha⟩ i (ψ.comp Algebra.TensorProduct.includeLeft)
      (by rw [hψi]; exact hx),
    kw_lrApt_toPointClass_eq_of_fac W K ⟨_, kw_lrDoc_pr₂_over W K i j a ha⟩ j
      ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight) (by rw [hψj]; exact hy)]

end Eval
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section Compat

variable [IsDomain R] [IsNoetherianRing R]

theorem kw_lrDens_outerCompat (hsm : Smooth π) (hgi : GeometricallyIntegral π)
    (hΔ : IsUnit W.Δ) (hclass : KwLRSixUClassEqAddMap W) : KwLROuterCompat W := by
  intro hcov hcompat ij ij'
  obtain ⟨i, j⟩ := ij
  obtain ⟨i', j'⟩ := ij'
  change pullback.fst ((C9).f (i, j)) ((C9).f (i', j')) ≫ kw_lrOuter_toE W hcov hcompat (i, j)
    = pullback.snd ((C9).f (i, j)) ((C9).f (i', j')) ≫ kw_lrOuter_toE W hcov hcompat (i', j')
  haveI : Smooth π := hsm
  haveI : GeometricallyIntegral π := hgi
  haveI : IsIntegral (pullback π π) := Density.isIntegral_pullback₂ π
  rcases isEmpty_or_nonempty ↥(pullback ((C9).f (i, j)) ((C9).f (i', j'))) with hV | hV
  · exact (isInitialOfIsEmpty (X := pullback ((C9).f (i, j)) ((C9).f (i', j')))).hom_ext _ _
  haveI : IsIntegral (pullback ((C9).f (i, j)) ((C9).f (i', j'))) :=
    isIntegral_of_isOpenImmersion (pullback.fst ((C9).f (i, j)) ((C9).f (i', j')) ≫ (C9).f (i, j))
  letI : Algebra R (pullback ((C9).f (i, j)) ((C9).f (i', j'))).functionField :=
    Density.functionFieldAlgebra
      (pullback.fst ((C9).f (i, j)) ((C9).f (i', j')) ≫ (C9).f (i, j) ≫ pullback.fst π π ≫ π)
  have halg := Density.genericInclusion_comp
      (pullback.fst ((C9).f (i, j)) ((C9).f (i', j')) ≫ (C9).f (i, j) ≫ pullback.fst π π ≫ π)
  have hΔK : algebraMap R (pullback ((C9).f (i, j)) ((C9).f (i', j'))).functionField W.Δ ≠ 0 :=
    (hΔ.map _).ne_zero
  have hsq : pullback.snd ((C9).f (i, j)) ((C9).f (i', j')) ≫ (C9).f (i', j')
      = pullback.fst ((C9).f (i, j)) ((C9).f (i', j')) ≫ (C9).f (i, j) :=
    pullback.condition.symm
  have hoverL : (pullback.fst ((C9).f (i, j)) ((C9).f (i', j'))
        ≫ kw_lrOuter_toE W hcov hcompat (i, j)) ≫ π
      = pullback.fst ((C9).f (i, j)) ((C9).f (i', j')) ≫ (C9).f (i, j) ≫ pullback.fst π π ≫ π := by
    rw [Category.assoc, kw_lrOuter_toE_over]
  have hoverR : (pullback.snd ((C9).f (i, j)) ((C9).f (i', j'))
        ≫ kw_lrOuter_toE W hcov hcompat (i', j')) ≫ π
      = pullback.fst ((C9).f (i, j)) ((C9).f (i', j')) ≫ (C9).f (i, j) ≫ pullback.fst π π ≫ π := by
    rw [Category.assoc, kw_lrOuter_toE_over, ← Category.assoc, hsq, Category.assoc]
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated π (hoverL.trans hoverR.symm)
    (Density.genericInclusion (pullback ((C9).f (i, j)) ((C9).f (i', j')))) ?_
  have haL : ((Density.genericInclusion (pullback ((C9).f (i, j)) ((C9).f (i', j'))) ≫ pullback.fst ((C9).f (i, j)) ((C9).f (i', j')))
        ≫ (C9).f (i, j) ≫ pullback.fst π π) ≫ π
      = kw_lrAptb_tF (R := R) (pullback ((C9).f (i, j)) ((C9).f (i', j'))).functionField := by
    simp only [Category.assoc] at halg ⊢
    exact halg
  have haR : ((Density.genericInclusion (pullback ((C9).f (i, j)) ((C9).f (i', j'))) ≫ pullback.snd ((C9).f (i, j)) ((C9).f (i', j')))
        ≫ (C9).f (i', j') ≫ pullback.fst π π) ≫ π
      = kw_lrAptb_tF (R := R) (pullback ((C9).f (i, j)) ((C9).f (i', j'))).functionField := by
    simp only [Category.assoc] at halg ⊢
    rw [← Category.assoc (pullback.snd _ _), hsq, Category.assoc]
    exact halg
  have hL := kw_lrDoc_eval W hcov hcompat _ i j hΔK hclass _ haL
  have hR := kw_lrDoc_eval W hcov hcompat _ i' j' hΔK hclass _ haR
  have hm₁ : (Density.genericInclusion (pullback ((C9).f (i, j)) ((C9).f (i', j')))
        ≫ pullback.snd ((C9).f (i, j)) ((C9).f (i', j'))) ≫ (C9).f (i', j') ≫ pullback.fst π π
      = (Density.genericInclusion (pullback ((C9).f (i, j)) ((C9).f (i', j')))
        ≫ pullback.fst ((C9).f (i, j)) ((C9).f (i', j'))) ≫ (C9).f (i, j) ≫ pullback.fst π π := by
    simp only [Category.assoc]
    rw [← pullback.condition_assoc]
  have hm₂ : (Density.genericInclusion (pullback ((C9).f (i, j)) ((C9).f (i', j')))
        ≫ pullback.snd ((C9).f (i, j)) ((C9).f (i', j'))) ≫ (C9).f (i', j') ≫ pullback.snd π π
      = (Density.genericInclusion (pullback ((C9).f (i, j)) ((C9).f (i', j')))
        ≫ pullback.fst ((C9).f (i, j)) ((C9).f (i', j'))) ≫ (C9).f (i, j) ≫ pullback.snd π π := by
    simp only [Category.assoc]
    rw [← pullback.condition_assoc]
  have hp₁ : (⟨_, haR⟩ : SchemeHomOver (kw_lrAptb_tF (R := R) _) π) = ⟨_, haL⟩ :=
    Subtype.ext hm₁
  have hp₂ : (⟨_, kw_lrDoc_pr₂_over W _ i' j' _ haR⟩ : SchemeHomOver (kw_lrAptb_tF (R := R) _) π)
      = ⟨_, kw_lrDoc_pr₂_over W _ i j _ haL⟩ :=
    Subtype.ext hm₂
  rw [hp₁, hp₂] at hR
  have hpt := kw_lrApt_toPointClass_injective W _ (hL.trans hR.symm)
  have := congrArg Subtype.val hpt
  simp only [Category.assoc] at this ⊢
  exact this

end Compat
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end MEGA_DensityOuterCompat_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section MEGA_KwLRAddBihomogeneous_lean

set_option autoImplicit false
set_option maxHeartbeats 25600000
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrAdd_c₂₁ kw_lrAdd_c₁₂ kw_lrAdd_starX kw_lrAdd_starY kw_lrAdd_starZ kw_lrAdd_X kw_lrAdd_Y kw_lrAdd_Z kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU KwLRSixUCoverage kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap KwLRPerChartCompat kw_lrPerChart_toE kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrOuter_toE KwLROuterCompat kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over"
p2m_open "WeierstrassProjModel"

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R
local notation "Xl" i => (X (Sum.inl i) : P₆)
local notation "Xr" i => (X (Sum.inr i) : P₆)

abbrev kw_lrBihom_wL : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

abbrev kw_lrBihom_wR : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

local notation "wL" => @kw_lrBihom_wL
local notation "wR" => @kw_lrBihom_wR

local macro "peel_bihom_L" : tactic =>
  `(tactic| repeat' with_reducible_and_instances first
    | apply IsWeightedHomogeneous.add | apply kw_lrBihom_sub | apply kw_lrBihom_neg
    | exact isWeightedHomogeneous_C _ _
    | exact kw_lrBihom_Xl_wL _ | exact kw_lrBihom_Xr_wL _
    | exact kw_lrBihom_Xl_wL_sq _ | exact kw_lrBihom_Xr_wL_sq _
    | refine IsWeightedHomogeneous.C_mul ?_ _
    | refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_Xl_wL _)
    | refine kw_lrBihom_mul0 ?_ (kw_lrBihom_Xr_wL _)
    | refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_Xl_wL_sq _)
    | refine kw_lrBihom_mul0 ?_ (kw_lrBihom_Xr_wL_sq _))

local macro "peel_bihom_R" : tactic =>
  `(tactic| repeat' with_reducible_and_instances first
    | apply IsWeightedHomogeneous.add | apply kw_lrBihom_sub | apply kw_lrBihom_neg
    | exact isWeightedHomogeneous_C _ _
    | exact kw_lrBihom_Xl_wR _ | exact kw_lrBihom_Xr_wR _
    | exact kw_lrBihom_Xl_wR_sq _ | exact kw_lrBihom_Xr_wR_sq _
    | refine IsWeightedHomogeneous.C_mul ?_ _
    | refine kw_lrBihom_mul0 ?_ (kw_lrBihom_Xl_wR _)
    | refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_Xr_wR _)
    | refine kw_lrBihom_mul0 ?_ (kw_lrBihom_Xl_wR_sq _)
    | refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_Xr_wR_sq _))

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end MEGA_KwLRAddBihomogeneous_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

section MEGA_SolShims

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel"
open scoped TensorProduct

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrAdd_c₂₁ kw_lrAdd_c₁₂ kw_lrAdd_starX kw_lrAdd_starY kw_lrAdd_starZ kw_lrAdd_X kw_lrAdd_Y kw_lrAdd_Z kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU KwLRSixUCoverage kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap KwLRPerChartCompat kw_lrPerChart_toE kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrOuter_toE KwLROuterCompat kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R]

theorem kw_lrApt_sixU_class_eq_addMap (W : WeierstrassCurve R) (K : Type u) [Field K] [Algebra R K]
    (hΔK : algebraMap R K W.Δ ≠ 0) (i j : Fin 3)
    (ψᵢ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] K)
    (ψⱼ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X j : MvPolynomial (Fin 3) R)) →ₐ[R] K)
    (l : Fin 3 ⊕ Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l))) :
    kw_lrApt_toPointClass W K
        ⟨Spec.map (CommRingCat.ofHom
            (IsLocalization.Away.lift (kw_lrSixU W i j l)
              (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrSixU_toE W i j l,
         kw_lrDcp_liftToE_over W K i j ψᵢ ψⱼ l hu⟩
      = (kw_lrApt_WF W K).addMap ⟦kw_lrApt_chartEval W K i ψᵢ⟧ ⟦kw_lrApt_chartEval W K j ψⱼ⟧ := by
  obtain ⟨k, ψₖ, hfac⟩ :=
    kw_lrApt_schemeHom_factor W K ⟨_, kw_lrDcp_liftToE_over W K i j ψᵢ ψⱼ l hu⟩
  rw [kw_lrApt_toPointClass_eq_of_fac W K _ k ψₖ hfac]
  exact WeierstrassProjModel.kw_a2_sixU_class_eq_addMap_of_delta_ne_zero W K hΔK i j ψᵢ ψⱼ l hu k ψₖ hfac

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

end MEGA_SolShims
p2m_reactivate "P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel.Density"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra _root_.WeierstrassProjModel _root_.P2MW.S_WeierstrassProjModel_outerCompat_of_smooth.WeierstrassProjModel in
theorem solution.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ) :
    KwLROuterCompat W :=
  WeierstrassProjModel.kw_lrDens_outerCompat W hsm hgi hΔ
    (fun K _ _ hΔK i j ψᵢ ψⱼ l hu => WeierstrassProjModel.kw_lrApt_sixU_class_eq_addMap W K hΔK i j ψᵢ ψⱼ l hu)

end S_WeierstrassProjModel_outerCompat_of_smooth
end P2MW
export P2MW.S_WeierstrassProjModel_outerCompat_of_smooth (solution)
