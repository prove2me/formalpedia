-- Prove2me | solution 1 for WeierstrassProjModel.kw_ev_triple_projections_chartFactor_pointClass_indep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/35029e43-821d-5c3d-96bc-bbf5f42927d0

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero
import Theorems.Thm_WeierstrassProjModel_sixU_toE_over
import Theorems.Thm_WeierstrassProjModel_exists_lrSixU_ne_zero_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Theorems.Thm_WeierstrassProjModel_kw_ev_genericPoint_chartFactor_pointClass_ne_zero
import Theorems.Thm_WeierstrassProjModel_kwYChartEval_gen_eq
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep

set_option Elab.async false

section MEGA_DensityKit_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU kw_lrSixU_toE kw_lrSixU_locMap kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwYChartEval kwYChartEval_section kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over exists_lrSixU_ne_zero_of_isElliptic isDomain_chartTensor_of_isElliptic kw_ev_genericPoint_chartFactor_pointClass_ne_zero projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kwYChartEval_gen_eq"
namespace Density
p2m_open "WeierstrassProjModel"

universe u

section GenericPoint

variable (X : Scheme.{u}) [IsIntegral X]

abbrev genericInclusion : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

theorem isDominant_genericInclusion : IsDominant (genericInclusion X) := by
  rw [isDominant_iff, DenseRange, Scheme.range_fromSpecStalk]
  refine Dense.mono (Set.singleton_subset_iff.mpr (specializes_refl _)) ?_
  exact dense_iff_closure_eq.mpr (genericPoint_spec X)

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

end

end MEGA_DensityKit_lean

section MEGA_ToEShim

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"
open scoped TensorProduct

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU kw_lrSixU_toE kw_lrSixU_locMap kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwYChartEval kwYChartEval_section kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over exists_lrSixU_ne_zero_of_isElliptic isDomain_chartTensor_of_isElliptic kw_ev_genericPoint_chartFactor_pointClass_ne_zero projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kwYChartEval_gen_eq"
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

end

end MEGA_ToEShim

section MEGA_KwLRAffinePtSetEquiv_lean

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial
open HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped WeierstrassCurve.Projective

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU kw_lrSixU_toE kw_lrSixU_locMap kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwYChartEval kwYChartEval_section kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over exists_lrSixU_ne_zero_of_isElliptic isDomain_chartTensor_of_isElliptic kw_ev_genericPoint_chartFactor_pointClass_ne_zero projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kwYChartEval_gen_eq"
p2m_open "WeierstrassProjModel"

p2m_open "WeierstrassProjModel P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel NeronModelInfra"

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

end WeierstrassProjModel

end
end MEGA_KwLRAffinePtSetEquiv_lean

section MEGA_DensityCompat_lean

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
open MvPolynomial HomogeneousLocalization WeierstrassCurve
open scoped TensorProduct

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU kw_lrSixU_toE kw_lrSixU_locMap kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwYChartEval kwYChartEval_section kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over exists_lrSixU_ne_zero_of_isElliptic isDomain_chartTensor_of_isElliptic kw_ev_genericPoint_chartFactor_pointClass_ne_zero projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kwYChartEval_gen_eq"
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

end Overlap

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

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end MEGA_DensityCompat_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

section MEGA_KwLRAffinePtAddEquivDischargeCore_lean

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option Elab.async false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial
open HomogeneousLocalization

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU kw_lrSixU_toE kw_lrSixU_locMap kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwYChartEval kwYChartEval_section kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over exists_lrSixU_ne_zero_of_isElliptic isDomain_chartTensor_of_isElliptic kw_ev_genericPoint_chartFactor_pointClass_ne_zero projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kwYChartEval_gen_eq"
p2m_open "WeierstrassProjModel"

p2m_open "WeierstrassProjModel P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel NeronModelInfra"

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
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end MapMulRaw
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"
end MEGA_KwLRAffinePtAddEquivDischargeCore_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

section MEGA_SolShims

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"
open scoped TensorProduct

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU kw_lrSixU_toE kw_lrSixU_locMap kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwYChartEval kwYChartEval_section kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over exists_lrSixU_ne_zero_of_isElliptic isDomain_chartTensor_of_isElliptic kw_ev_genericPoint_chartFactor_pointClass_ne_zero projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kwYChartEval_gen_eq"
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
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end MEGA_SolShims
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

section MEGA_DensityOuterCompat_lean

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
open MvPolynomial HomogeneousLocalization WeierstrassCurve
open scoped TensorProduct

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU kw_lrSixU_toE kw_lrSixU_locMap kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwYChartEval kwYChartEval_section kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over exists_lrSixU_ne_zero_of_isElliptic isDomain_chartTensor_of_isElliptic kw_ev_genericPoint_chartFactor_pointClass_ne_zero projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kwYChartEval_gen_eq"
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
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end MEGA_DensityOuterCompat_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
open MvPolynomial HomogeneousLocalization WeierstrassCurve
open scoped TensorProduct

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrSixU kw_lrSixU_toE kw_lrSixU_locMap kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwYChartEval kwYChartEval_section kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_sixU_class_eq_addMap_of_delta_ne_zero sixU_toE_over exists_lrSixU_ne_zero_of_isElliptic isDomain_chartTensor_of_isElliptic kw_ev_genericPoint_chartFactor_pointClass_ne_zero projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kwYChartEval_gen_eq"
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
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover

section ZeroPoint

variable (K : Type u) [Field K] [Algebra R K]

def kw_trp_zeroPt : Spec (CommRingCat.of K) ⟶ E :=
  Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (kwZeroSect R W).1

theorem kw_trp_zeroPt_over :
    kw_trp_zeroPt W K ≫ π = kw_lrAptb_tF (R := R) K := by
  rw [kw_trp_zeroPt, Category.assoc, (kwZeroSect R W).2, Category.comp_id]

def kw_trp_zeroChartHom : (𝒜 (1 : Fin 3)) →ₐ[R] K :=
  (Algebra.ofId R K).comp
    { kwYChartEval R W with
      commutes' := fun r => RingHom.congr_fun (kwYChartEval_section R W) r }

theorem kw_trp_zeroPt_fac :
    kw_trp_zeroPt W K
      = Spec.map (CommRingCat.ofHom (kw_trp_zeroChartHom W K).toRingHom) ≫ (coverE).f (1 : Fin 3) := by
  show Spec.map (CommRingCat.ofHom (algebraMap R K))
      ≫ Spec.map (CommRingCat.ofHom (kwYChartEval R W)) ≫ _ = _
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  rfl

theorem kw_trp_zeroChartHom_chartEval :
    kw_lrApt_chartEval W K 1 (kw_trp_zeroChartHom W K) = ![(0 : K), 1, 0] := by
  funext k
  show algebraMap R K (kwYChartEval R W (kw_lrChart_gen W 1 k)) = _
  rw [kwYChartEval_gen_eq]
  fin_cases k
  · exact map_zero _
  · exact map_one _
  · exact map_zero _

theorem kw_trp_toPointClass_zeroPt (hΔK : algebraMap R K W.Δ ≠ 0) :
    kw_lrApt_toPointClass W K ⟨kw_trp_zeroPt W K, kw_trp_zeroPt_over W K⟩
      = ⟦![(0 : K), 1, 0]⟧ := by
  rw [kw_lrApt_toPointClass_eq_of_fac W K _ 1 (kw_trp_zeroChartHom W K)
    (kw_trp_zeroPt_fac W K), kw_trp_zeroChartHom_chartEval]

end ZeroPoint
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

section GenericNeZero

variable [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]

theorem kw_trp_genericPoint_ne_zeroPt :
    haveI : Smooth π := (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
    haveI : GeometricallyIntegral π :=
      kw_hgi_geometricallyIntegral_of_baseChangeIso W (projModel_pullback_iso_baseChange W.toProjective)
    haveI : IsIntegral E := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian π
    letI : Algebra R (E).functionField :=
      (Spec.preimage ((E).fromSpecStalk (genericPoint E) ≫ π)).hom.toAlgebra
    (E).fromSpecStalk (genericPoint E) ≠ kw_trp_zeroPt W (E).functionField := by
  haveI : Smooth π := (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI : GeometricallyIntegral π :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W (projModel_pullback_iso_baseChange W.toProjective)
  haveI : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : IsIntegral E := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian π
  letI : Algebra R (E).functionField :=
    (Spec.preimage ((E).fromSpecStalk (genericPoint E) ≫ π)).hom.toAlgebra
  intro heq
  obtain ⟨i, ψ, hfac, hne⟩ := kw_ev_genericPoint_chartFactor_pointClass_ne_zero W
  have hΔK : algebraMap R (E).functionField W.Δ ≠ 0 := (W.isUnit_Δ.map _).ne_zero
  have hover : (E).fromSpecStalk (genericPoint E) ≫ π = kw_lrAptb_tF (R := R) (E).functionField := by
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R (E).functionField))
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  have h1 := kw_lrApt_toPointClass_eq_of_fac W (E).functionField ⟨_, hover⟩ i ψ hfac
  have h2 : (⟨_, hover⟩ : SchemeHomOver (kw_lrAptb_tF (R := R) (E).functionField) π)
      = ⟨kw_trp_zeroPt W (E).functionField, kw_trp_zeroPt_over W (E).functionField⟩ :=
    Subtype.ext heq
  rw [h2, kw_trp_toPointClass_zeroPt W _ hΔK] at h1
  exact hne h1.symm

end GenericNeZero
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

section Triple

variable [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]

set_option quotPrecheck false in
local notation "X3" => (pullback (pullback.fst (projModelStrCR W.toProjective)
  (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
  : Scheme)
set_option quotPrecheck false in
local notation "p₁₂" => pullback.fst (pullback.fst (projModelStrCR W.toProjective)
  (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
set_option quotPrecheck false in
local notation "p₃" => pullback.snd (pullback.fst (projModelStrCR W.toProjective)
  (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)

theorem kw_trp_ext [IsIntegral X3] (f g : X3 ⟶ E) (hf : f ≫ π = g ≫ π)
    (h : (X3).fromSpecStalk (genericPoint X3) ≫ f = (X3).fromSpecStalk (genericPoint X3) ≫ g) :
    f = g := by
  haveI := Density.isDominant_genericInclusion (X3)
  exact ext_of_isDominant_of_isSeparated π hf (Density.genericInclusion X3) h

variable (K : Type u) [Field K] [Algebra R K]

def kw_trp_pt (u v w : SchemeHomOver (kw_lrAptb_tF (R := R) K) π) :
    Spec (CommRingCat.of K) ⟶ X3 :=
  pullback.lift (pullback.lift u.1 v.1 (u.2.trans v.2.symm)) w.1
    (by rw [pullback.lift_fst_assoc, u.2, w.2])

theorem kw_trp_pt_pr₁ (u v w : SchemeHomOver (kw_lrAptb_tF (R := R) K) π) :
    kw_trp_pt W K u v w ≫ p₁₂ ≫ pullback.fst π π = u.1 := by
  rw [kw_trp_pt, pullback.lift_fst_assoc, pullback.lift_fst]

theorem kw_trp_pt_pr₂ (u v w : SchemeHomOver (kw_lrAptb_tF (R := R) K) π) :
    kw_trp_pt W K u v w ≫ p₁₂ ≫ pullback.snd π π = v.1 := by
  rw [kw_trp_pt, pullback.lift_fst_assoc, pullback.lift_snd]

theorem kw_trp_pt_pr₃ (u v w : SchemeHomOver (kw_lrAptb_tF (R := R) K) π) :
    kw_trp_pt W K u v w ≫ p₃ = w.1 := by
  rw [kw_trp_pt, pullback.lift_snd]

omit [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] in
theorem kw_trp_pr₁_over : (p₁₂ ≫ pullback.fst π π) ≫ π = p₃ ≫ π :=
  (Category.assoc _ _ _).trans pullback.condition

omit [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] in
theorem kw_trp_pr₂_over : (p₁₂ ≫ pullback.snd π π) ≫ π = p₃ ≫ π :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition.symm).trans pullback.condition)

theorem kw_trp_generic_pr₁_ne_pr₂ [IsIntegral X3] :
    (X3).fromSpecStalk (genericPoint X3) ≫ p₁₂ ≫ pullback.fst π π
      ≠ (X3).fromSpecStalk (genericPoint X3) ≫ p₁₂ ≫ pullback.snd π π := by
  intro h
  have hfg : p₁₂ ≫ pullback.fst π π = p₁₂ ≫ pullback.snd π π :=
    kw_trp_ext W _ _ ((kw_trp_pr₁_over W).trans (kw_trp_pr₂_over W).symm) h

  haveI : Smooth π := (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI : GeometricallyIntegral π :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W (projModel_pullback_iso_baseChange W.toProjective)
  haveI : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : IsIntegral E := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian π
  letI : Algebra R (E).functionField :=
    (Spec.preimage ((E).fromSpecStalk (genericPoint E) ≫ π)).hom.toAlgebra
  have hover : (E).fromSpecStalk (genericPoint E) ≫ π = kw_lrAptb_tF (R := R) (E).functionField := by
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R (E).functionField))
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  let ηE : SchemeHomOver (kw_lrAptb_tF (R := R) (E).functionField) π := ⟨_, hover⟩
  let O : SchemeHomOver (kw_lrAptb_tF (R := R) (E).functionField) π :=
    ⟨kw_trp_zeroPt W (E).functionField, kw_trp_zeroPt_over W (E).functionField⟩
  have hz := congrArg (kw_trp_pt W (E).functionField ηE O O ≫ ·) hfg
  beta_reduce at hz
  rw [kw_trp_pt_pr₁, kw_trp_pt_pr₂] at hz
  exact kw_trp_genericPoint_ne_zeroPt W hz

theorem kw_trp_generic_pr₂_ne_pr₃ [IsIntegral X3] :
    (X3).fromSpecStalk (genericPoint X3) ≫ p₁₂ ≫ pullback.snd π π
      ≠ (X3).fromSpecStalk (genericPoint X3) ≫ p₃ := by
  intro h
  have hfg : p₁₂ ≫ pullback.snd π π = p₃ :=
    kw_trp_ext W _ _ (kw_trp_pr₂_over W) h
  haveI : Smooth π := (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI : GeometricallyIntegral π :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W (projModel_pullback_iso_baseChange W.toProjective)
  haveI : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : IsIntegral E := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian π
  letI : Algebra R (E).functionField :=
    (Spec.preimage ((E).fromSpecStalk (genericPoint E) ≫ π)).hom.toAlgebra
  have hover : (E).fromSpecStalk (genericPoint E) ≫ π = kw_lrAptb_tF (R := R) (E).functionField := by
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R (E).functionField))
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  let ηE : SchemeHomOver (kw_lrAptb_tF (R := R) (E).functionField) π := ⟨_, hover⟩
  let O : SchemeHomOver (kw_lrAptb_tF (R := R) (E).functionField) π :=
    ⟨kw_trp_zeroPt W (E).functionField, kw_trp_zeroPt_over W (E).functionField⟩
  have hz := congrArg (kw_trp_pt W (E).functionField O ηE O ≫ ·) hfg
  beta_reduce at hz
  rw [kw_trp_pt_pr₂, kw_trp_pt_pr₃] at hz
  exact kw_trp_genericPoint_ne_zeroPt W hz

theorem kw_trp_generic_ne_zeroPt [IsIntegral X3] [IsIntegral E] (T : X3 ⟶ E)
    (hT : T ≫ π = p₃ ≫ π)
    (s : Spec (CommRingCat.of (E).functionField) ⟶ X3)
    (hs : s ≫ T = (E).fromSpecStalk (genericPoint E)) :
    letI : Algebra R (X3).functionField :=
      (Spec.preimage ((X3).fromSpecStalk (genericPoint X3) ≫ p₃ ≫ π)).hom.toAlgebra
    (X3).fromSpecStalk (genericPoint X3) ≫ T ≠ kw_trp_zeroPt W (X3).functionField := by
  letI : Algebra R (X3).functionField :=
    (Spec.preimage ((X3).fromSpecStalk (genericPoint X3) ≫ p₃ ≫ π)).hom.toAlgebra
  intro h
  have hK : kw_trp_zeroPt W (X3).functionField
      = ((X3).fromSpecStalk (genericPoint X3) ≫ p₃ ≫ π) ≫ (kwZeroSect R W).1 := by
    show Spec.map (CommRingCat.ofHom (algebraMap R (X3).functionField)) ≫ _ = _
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfg : T = T ≫ π ≫ (kwZeroSect R W).1 := by
    refine kw_trp_ext W _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, (kwZeroSect R W).2, Category.comp_id]
    · rw [h, hK, ← hT]; simp only [Category.assoc]
  letI : Algebra R (E).functionField :=
    (Spec.preimage ((E).fromSpecStalk (genericPoint E) ≫ π)).hom.toAlgebra
  have hz := congrArg (s ≫ ·) hfg
  beta_reduce at hz
  rw [hs, ← Category.assoc, hs] at hz
  apply kw_trp_genericPoint_ne_zeroPt W
  convert hz using 1 <;> try rfl
  show Spec.map (CommRingCat.ofHom (algebraMap R (E).functionField)) ≫ _ = _
  rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc]

omit [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] in

theorem kw_trp_p₁₂_surjective : Function.Surjective p₁₂ := by
  let s : pullback π π ⟶ X3 := pullback.lift (𝟙 _) (pullback.fst π π) (by rw [Category.id_comp])
  have hs : s ≫ p₁₂ = 𝟙 _ := pullback.lift_fst _ _ _
  intro y
  exact ⟨s y, by rw [← Scheme.Hom.comp_apply, hs]; rfl⟩

def kw_trp_q₂₃ : X3 ⟶ pullback π π :=
  pullback.lift (p₁₂ ≫ pullback.snd π π) p₃ (kw_trp_pr₂_over W)

omit [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] in
theorem kw_trp_q₂₃_fst : kw_trp_q₂₃ W ≫ pullback.fst π π = p₁₂ ≫ pullback.snd π π :=
  pullback.lift_fst _ _ _

omit [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] in
theorem kw_trp_q₂₃_snd : kw_trp_q₂₃ W ≫ pullback.snd π π = p₃ :=
  pullback.lift_snd _ _ _

omit [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] in

theorem kw_trp_q₂₃_surjective : Function.Surjective (kw_trp_q₂₃ W) := by
  let s : pullback π π ⟶ X3 :=
    pullback.lift (pullback.lift (pullback.fst π π) (pullback.fst π π) rfl) (pullback.snd π π)
      (by rw [pullback.lift_fst_assoc]; exact pullback.condition)
  have hs : s ≫ kw_trp_q₂₃ W = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, kw_trp_q₂₃_fst, pullback.lift_fst_assoc, pullback.lift_snd,
        Category.id_comp]
    · rw [Category.assoc, kw_trp_q₂₃_snd, pullback.lift_snd, Category.id_comp]
  intro y
  exact ⟨s y, by rw [← Scheme.Hom.comp_apply, hs]; rfl⟩

end Triple
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

section GenericTransport

theorem kw_trp_apply_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : Function.Surjective f) :
    f (genericPoint X) = genericPoint Y := by
  refine IsGenericPoint.eq ?_ (genericPoint_spec Y)
  show closure ({f (genericPoint X)} : Set Y) = Set.univ
  refine Set.eq_univ_of_univ_subset ?_
  calc (Set.univ : Set Y) = f '' Set.univ := (Set.image_univ_of_surjective hf).symm
    _ = f '' closure {genericPoint X} := by rw [genericPoint_closure]
    _ ⊆ closure (f '' {genericPoint X}) := image_closure_subset_closure_image f.continuous
    _ = closure {f (genericPoint X)} := by rw [Set.image_singleton]

theorem kw_trp_injective_of_fac {Y : Scheme.{u}} [IsIntegral Y] {K A : Type u} [Field K]
    [CommRing A] [IsDomain A]
    (k : Spec (CommRingCat.of K) ⟶ Y) (hk : k (IsLocalRing.closedPoint K) = genericPoint Y)
    (g : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion g] (ρ : A →+* K)
    (hfac : Spec.map (CommRingCat.ofHom ρ) ≫ g = k) : Function.Injective ρ := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hq : g (Spec.map (CommRingCat.ofHom ρ) (IsLocalRing.closedPoint K)) = genericPoint Y := by
    rw [← Scheme.Hom.comp_apply, hfac, hk]
  have hmem : a ∈ (Spec.map (CommRingCat.ofHom ρ) (IsLocalRing.closedPoint K)).asIdeal := by
    change ρ a ∈ (IsLocalRing.closedPoint K).asIdeal
    rw [ha]; exact Ideal.zero_mem _
  let b : Spec (CommRingCat.of A) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A)
  have hsp : g (Spec.map (CommRingCat.ofHom ρ) (IsLocalRing.closedPoint K)) ⤳ g b :=
    hq ▸ genericPoint_specializes (g b)
  have hsp' : Spec.map (CommRingCat.ofHom ρ) (IsLocalRing.closedPoint K) ⤳ b :=
    g.isOpenEmbedding.isInducing.specializes_iff.mp hsp
  have hle := (PrimeSpectrum.le_iff_specializes _ b).mpr hsp'
  exact (Submodule.mem_bot (R := A)).mp (hle hmem)

end GenericTransport
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

section Restrict

variable [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]

set_option quotPrecheck false in
local notation "X3" => (pullback (pullback.fst (projModelStrCR W.toProjective)
  (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
  : Scheme)
set_option quotPrecheck false in
local notation "p₁₂" => pullback.fst (pullback.fst (projModelStrCR W.toProjective)
  (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
set_option quotPrecheck false in
local notation "p₃" => pullback.snd (pullback.fst (projModelStrCR W.toProjective)
  (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
set_option quotPrecheck false in
local notation "C9" => kwProjPullbackOpenCoverCR R W.toProjective
set_option quotPrecheck false in
local notation "chartIso" => kwProjPullbackChartIsoCR R W.toProjective

def kw_trp_ιV (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) :
    Spec (CommRingCat.of (Localization.Away (kw_lrSixU W i j l))) ⟶ pullback π π :=
  kw_lrSixU_locMap W i j l ≫ (chartIso i j).inv ≫ (C9).f (i, j)

scoped instance kw_trp_ιV_isOpenImmersion (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) :
    IsOpenImmersion (kw_trp_ιV W i j l) := by
  unfold kw_trp_ιV; infer_instance

omit [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] in

theorem kw_trp_pair_fac (K : Type u) [Field K] [Algebra R K]
    (x : Spec (CommRingCat.of K) ⟶ pullback π π) (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] K) (ψⱼ : (𝒜 j) →ₐ[R] K)
    (hx : x ≫ pullback.fst π π = Spec.map (CommRingCat.ofHom ψᵢ.toRingHom) ≫ (coverE).f i)
    (hy : x ≫ pullback.snd π π = Spec.map (CommRingCat.ofHom ψⱼ.toRingHom) ≫ (coverE).f j) :
    x = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
          ≫ (chartIso i j).inv ≫ (C9).f (i, j) := by
  have eᵢ : ψᵢ.toRingHom = (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j)) :=
    congrArg AlgHom.toRingHom (Algebra.TensorProduct.productMap_left ψᵢ ψⱼ).symm
  have eⱼ : ψⱼ.toRingHom = (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := 𝒜 i) (B := 𝒜 j)).toRingHom :=
    congrArg AlgHom.toRingHom (Algebra.TensorProduct.productMap_right ψᵢ ψⱼ).symm
  apply pullback.hom_ext
  · rw [hx, eᵢ, CommRingCat.ofHom_comp, Spec.map_comp]
    simp only [Category.assoc]
    rw [kw_lrDoc_coverf_fst]
    erw [reassoc_of% (kw_lrApt_chartIso_inv_fst W i j)]
    rfl
  · rw [hy, eⱼ, CommRingCat.ofHom_comp, Spec.map_comp]
    simp only [Category.assoc]
    rw [kw_lrDoc_coverf_snd]
    erw [reassoc_of% (kw_lrApt_chartIso_inv_snd W i j)]
    rfl

omit [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] in
theorem kw_trp_lift_ιV {K : Type u} [CommRing K] (i j : Fin 3) (l : Fin 3 ⊕ Fin 3)
    (ρ : (𝒜 i) ⊗[R] (𝒜 j) →+* K) (hu : IsUnit (ρ (kw_lrSixU W i j l))) :
    Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (kw_lrSixU W i j l) (g := ρ) hu))
        ≫ kw_trp_ιV W i j l
      = Spec.map (CommRingCat.ofHom ρ) ≫ (chartIso i j).inv ≫ (C9).f (i, j) := by
  rw [kw_trp_ιV, ← Category.assoc, kw_lrSixU_locMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp]

omit [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] in

theorem kw_trp_isSeparated : (E).IsSeparated :=
  ⟨by rw [Limits.terminal.hom_ext (Limits.terminal.from E) (π ≫ Limits.terminal.from _)]
      infer_instance⟩

theorem kw_trp_restrict [IsIntegral X3] (Q : X3 ⟶ pullback π π) (T : X3 ⟶ E) (i j : Fin 3)
    (ρ : (𝒜 i) ⊗[R] (𝒜 j) →+* (X3).functionField) (l : Fin 3 ⊕ Fin 3)
    (hu : IsUnit (ρ (kw_lrSixU W i j l)))
    (hQ : (X3).fromSpecStalk (genericPoint X3) ≫ Q
      = Spec.map (CommRingCat.ofHom ρ) ≫ (chartIso i j).inv ≫ (C9).f (i, j))
    (hz : Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (kw_lrSixU W i j l) (g := ρ) hu))
        ≫ kw_lrSixU_toE W i j l = (X3).fromSpecStalk (genericPoint X3) ≫ T)
    (s : Spec (CommRingCat.of (X3).functionField) ⟶ X3)
    (hs : s ≫ Q = (X3).fromSpecStalk (genericPoint X3) ≫ Q) :
    Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (kw_lrSixU W i j l) (g := ρ) hu))
        ≫ kw_lrSixU_toE W i j l = s ≫ T := by
  have hfac : Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (kw_lrSixU W i j l) (g := ρ) hu))
        ≫ kw_trp_ιV W i j l
      = (X3).fromSpecStalk (genericPoint X3) ≫ Q := by
    rw [kw_trp_lift_ιV, hQ]
  obtain ⟨ηt, hηt₁, hηt₂⟩ : ∃ ηt : Spec (CommRingCat.of (X3).functionField)
      ⟶ pullback (kw_trp_ιV W i j l) Q,
      ηt ≫ pullback.fst (kw_trp_ιV W i j l) Q = Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (kw_lrSixU W i j l) (g := ρ) hu))
      ∧ ηt ≫ pullback.snd (kw_trp_ιV W i j l) Q = (X3).fromSpecStalk (genericPoint X3) :=
    ⟨pullback.lift _ _ hfac, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨st, hst₁, hst₂⟩ : ∃ st : Spec (CommRingCat.of (X3).functionField)
      ⟶ pullback (kw_trp_ιV W i j l) Q,
      st ≫ pullback.fst (kw_trp_ιV W i j l) Q = Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (kw_lrSixU W i j l) (g := ρ) hu))
      ∧ st ≫ pullback.snd (kw_trp_ιV W i j l) Q = s :=
    ⟨pullback.lift _ _ (hfac.trans hs.symm), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  haveI : IsReduced (pullback (kw_trp_ιV W i j l) Q) :=
    isReduced_of_isOpenImmersion (pullback.snd (kw_trp_ιV W i j l) Q)
  haveI : (E).IsSeparated := kw_trp_isSeparated W
  haveI : IsDominant ηt := by
    refine ⟨?_⟩
    rw [DenseRange, dense_iff_inter_open]
    rintro O hO ⟨o, ho⟩
    have hOimg : IsOpen ((pullback.snd (kw_trp_ιV W i j l) Q) '' O) :=
      (pullback.snd (kw_trp_ιV W i j l) Q).isOpenEmbedding.isOpenMap _ hO
    obtain ⟨o', ho', he⟩ : genericPoint X3 ∈ (pullback.snd (kw_trp_ιV W i j l) Q) '' O :=
      (genericPoint_specializes ((pullback.snd (kw_trp_ιV W i j l) Q) o)).mem_open hOimg
        ⟨o, ho, rfl⟩
    refine ⟨o', ho', IsLocalRing.closedPoint _, ?_⟩
    apply (pullback.snd (kw_trp_ιV W i j l) Q).isOpenEmbedding.injective
    rw [he, ← Scheme.Hom.comp_apply, hηt₂, Scheme.fromSpecStalk_closedPoint]
  have hfg : pullback.fst (kw_trp_ιV W i j l) Q ≫ kw_lrSixU_toE W i j l
      = pullback.snd (kw_trp_ιV W i j l) Q ≫ T :=
    ext_of_isDominant ηt (by rw [← Category.assoc, hηt₁, ← Category.assoc, hηt₂, hz])
  refine (congrArg (· ≫ kw_lrSixU_toE W i j l) hst₁).symm.trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (st ≫ ·) hfg).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ T) hst₂)

end Restrict
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

section Main

set_option quotPrecheck false in
local notation "X₃" => (pullback (pullback.fst (projModelStrCR W.toProjective)
  (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
  : Scheme)
set_option quotPrecheck false in
local notation "p₁₂" => pullback.fst (pullback.fst (projModelStrCR W.toProjective)
  (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
set_option quotPrecheck false in
local notation "p₃" => pullback.snd (pullback.fst (projModelStrCR W.toProjective)
  (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
set_option quotPrecheck false in
local notation "C9" => kwProjPullbackOpenCoverCR R W.toProjective
set_option quotPrecheck false in
local notation "chartIso" => kwProjPullbackChartIsoCR R W.toProjective

set_option maxHeartbeats 6400000 in

theorem kw_ev_trp_main
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    haveI : Smooth (projModelStrCR W.toProjective) :=
      (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
    haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
      kw_hgi_geometricallyIntegral_of_baseChangeIso W
        (projModel_pullback_iso_baseChange W.toProjective)
    haveI : IsIntegral X₃ := by
      haveI : IsLocallyNoetherian (projModelCR W.toProjective) :=
        LocallyOfFiniteType.isLocallyNoetherian (projModelStrCR W.toProjective)
      haveI : IsIntegral (projModelCR W.toProjective) :=
        GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
      haveI : GeometricallyIntegral (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
      haveI : IsIntegral ↑(pullback (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
          (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
      haveI : IsLocallyNoetherian ↑(pullback (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
      haveI : GeometricallyIntegral (pullback.fst (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
      exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
        (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
    letI : Algebra R (X₃).functionField :=
      (Spec.preimage ((X₃).fromSpecStalk (genericPoint X₃)
        ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective)).hom.toAlgebra
    ∃ (ia : Fin 3) (ψa : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ia : MvPolynomial (Fin 3) R)) →ₐ[R] (X₃).functionField)
      (ib : Fin 3) (ψb : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ib : MvPolynomial (Fin 3) R)) →ₐ[R] (X₃).functionField)
      (ic : Fin 3) (ψc : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ic : MvPolynomial (Fin 3) R)) →ₐ[R] (X₃).functionField),
      ((X₃).fromSpecStalk (genericPoint X₃)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψa.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ia)
      ∧ ((X₃).fromSpecStalk (genericPoint X₃)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψb.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ib)
      ∧ ((X₃).fromSpecStalk (genericPoint X₃)
          ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψc.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ic)
      ∧ ((⟦kw_lrApt_chartEval W (X₃).functionField ia ψa⟧
            : WeierstrassCurve.Projective.PointClass (X₃).functionField)
          ≠ ⟦kw_lrApt_chartEval W (X₃).functionField ib ψb⟧)
      ∧ ((⟦kw_lrApt_chartEval W (X₃).functionField ib ψb⟧
            : WeierstrassCurve.Projective.PointClass (X₃).functionField)
          ≠ ⟦kw_lrApt_chartEval W (X₃).functionField ic ψc⟧)
      ∧ ((kw_lrApt_WF W (X₃).functionField).addMap
            ⟦kw_lrApt_chartEval W (X₃).functionField ia ψa⟧
            ⟦kw_lrApt_chartEval W (X₃).functionField ib ψb⟧
          ≠ ⟦kw_lrApt_chartEval W (X₃).functionField ic ψc⟧)
      ∧ ((⟦kw_lrApt_chartEval W (X₃).functionField ia ψa⟧
            : WeierstrassCurve.Projective.PointClass (X₃).functionField)
          ≠ (kw_lrApt_WF W (X₃).functionField).addMap
              ⟦kw_lrApt_chartEval W (X₃).functionField ib ψb⟧
              ⟦kw_lrApt_chartEval W (X₃).functionField ic ψc⟧) := by
  haveI : Smooth π := (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI : GeometricallyIntegral π :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W (projModel_pullback_iso_baseChange W.toProjective)
  haveI : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : IsIntegral E := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian π
  haveI : GeometricallyIntegral (pullback.fst π π) :=
    MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral π›
  haveI : IsIntegral ↑(pullback π π) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst π π)
  haveI : IsLocallyNoetherian ↑(pullback π π) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst π π)
  haveI : GeometricallyIntegral p₁₂ :=
    MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral π›
  haveI : IsIntegral X₃ := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p₁₂
  letI : Algebra R (X₃).functionField :=
    (Spec.preimage ((X₃).fromSpecStalk (genericPoint X₃) ≫ p₃ ≫ π)).hom.toAlgebra
  have hΔK : algebraMap R (X₃).functionField W.Δ ≠ 0 := (W.isUnit_Δ.map _).ne_zero
  have hover₃ : ((X₃).fromSpecStalk (genericPoint X₃) ≫ p₃) ≫ π
      = kw_lrAptb_tF (R := R) (X₃).functionField := by
    refine (Category.assoc _ _ _).trans ?_
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R (X₃).functionField))
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hover₁ : ((X₃).fromSpecStalk (genericPoint X₃) ≫ p₁₂ ≫ pullback.fst π π) ≫ π
      = kw_lrAptb_tF (R := R) (X₃).functionField :=
    (Category.assoc _ _ _).trans ((congrArg ((X₃).fromSpecStalk (genericPoint X₃) ≫ ·) (kw_trp_pr₁_over W)).trans
      ((Category.assoc _ _ _).symm.trans hover₃))
  have hover₂ : ((X₃).fromSpecStalk (genericPoint X₃) ≫ p₁₂ ≫ pullback.snd π π) ≫ π
      = kw_lrAptb_tF (R := R) (X₃).functionField :=
    (Category.assoc _ _ _).trans ((congrArg ((X₃).fromSpecStalk (genericPoint X₃) ≫ ·) (kw_trp_pr₂_over W)).trans
      ((Category.assoc _ _ _).symm.trans hover₃))

  letI : Algebra R (E).functionField :=
    (Spec.preimage ((E).fromSpecStalk (genericPoint E) ≫ π)).hom.toAlgebra
  have hoverE : (E).fromSpecStalk (genericPoint E) ≫ π
      = kw_lrAptb_tF (R := R) (E).functionField := by
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R (E).functionField))
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  let ηE : SchemeHomOver (kw_lrAptb_tF (R := R) (E).functionField) π := ⟨_, hoverE⟩
  let OE : SchemeHomOver (kw_lrAptb_tF (R := R) (E).functionField) π :=
    ⟨kw_trp_zeroPt W (E).functionField, kw_trp_zeroPt_over W (E).functionField⟩

  let x₁ : SchemeHomOver (kw_lrAptb_tF (R := R) (X₃).functionField) π := ⟨_, hover₁⟩
  let x₂ : SchemeHomOver (kw_lrAptb_tF (R := R) (X₃).functionField) π := ⟨_, hover₂⟩
  let x₃ : SchemeHomOver (kw_lrAptb_tF (R := R) (X₃).functionField) π := ⟨_, hover₃⟩
  let O : SchemeHomOver (kw_lrAptb_tF (R := R) (X₃).functionField) π :=
    ⟨kw_trp_zeroPt W (X₃).functionField, kw_trp_zeroPt_over W (X₃).functionField⟩
  refine (kw_lrApt_schemeHom_factor W (X₃).functionField x₁).elim fun ia hia => ?_
  refine hia.elim fun ψa ha => ?_
  refine (kw_lrApt_schemeHom_factor W (X₃).functionField x₂).elim fun ib hib => ?_
  refine hib.elim fun ψb hb => ?_
  refine (kw_lrApt_schemeHom_factor W (X₃).functionField x₃).elim fun ic hic => ?_
  refine hic.elim fun ψc hc => ?_
  have hca := kw_lrApt_toPointClass_eq_of_fac W (X₃).functionField x₁ ia ψa ha
  have hcb := kw_lrApt_toPointClass_eq_of_fac W (X₃).functionField x₂ ib ψb hb
  have hcc := kw_lrApt_toPointClass_eq_of_fac W (X₃).functionField x₃ ic ψc hc
  refine ⟨ia, ψa, ib, ψb, ic, ψc, ha, hb, hc, ?_, ?_, ?_, ?_⟩
  ·
    intro h
    have := kw_lrApt_toPointClass_injective W _ (hca.trans (h.trans hcb.symm))
    exact kw_trp_generic_pr₁_ne_pr₂ W (congrArg Subtype.val this)
  ·
    intro h
    have := kw_lrApt_toPointClass_injective W _ (hcb.trans (h.trans hcc.symm))
    exact kw_trp_generic_pr₂_ne_pr₃ W (congrArg Subtype.val this)
  ·
    intro h
    have hQ := kw_trp_pair_fac W (X₃).functionField ((X₃).fromSpecStalk (genericPoint X₃) ≫ p₁₂) ia ib ψa ψb
      ((Category.assoc _ _ _).trans ha) ((Category.assoc _ _ _).trans hb)
    have hgen : ((X₃).fromSpecStalk (genericPoint X₃) ≫ p₁₂) (IsLocalRing.closedPoint _) = genericPoint (pullback π π : Scheme.{u}) := by
      rw [Scheme.Hom.comp_apply]
      exact (congrArg p₁₂ (Scheme.fromSpecStalk_closedPoint (x := genericPoint X₃))).trans
        (kw_trp_apply_genericPoint _ (kw_trp_p₁₂_surjective W))
    haveI : IsDomain ((𝒜 ia) ⊗[R] (𝒜 ib)) := isDomain_chartTensor_of_isElliptic W ia ib
    have hinj : Function.Injective (Algebra.TensorProduct.productMap ψa ψb).toRingHom :=
      kw_trp_injective_of_fac ((X₃).fromSpecStalk (genericPoint X₃) ≫ p₁₂) hgen ((chartIso ia ib).inv ≫ (C9).f (ia, ib)) _ hQ.symm
    refine (exists_lrSixU_ne_zero_of_isElliptic W ia ib).elim fun l hl0 => ?_
    have hu : IsUnit ((Algebra.TensorProduct.productMap ψa ψb) (kw_lrSixU W ia ib l)) :=
      isUnit_iff_ne_zero.mpr fun h0 => hl0 (hinj (h0.trans (map_zero _).symm))
    have hz := kw_lrApt_sixU_class_eq_addMap W (X₃).functionField hΔK ia ib ψa ψb l hu
    have heq := congrArg Subtype.val
      (kw_lrApt_toPointClass_injective W _ (hz.trans (h.trans hcc.symm)))
    have hs : kw_trp_pt W (X₃).functionField x₁ x₂ O ≫ p₁₂ = (X₃).fromSpecStalk (genericPoint X₃) ≫ p₁₂ :=
      pullback.hom_ext
        ((Category.assoc _ _ _).trans ((kw_trp_pt_pr₁ W _ x₁ x₂ O).trans
          (Category.assoc _ _ _).symm))
        ((Category.assoc _ _ _).trans ((kw_trp_pt_pr₂ W _ x₁ x₂ O).trans
          (Category.assoc _ _ _).symm))
    have hres := kw_trp_restrict W p₁₂ p₃ ia ib
      (Algebra.TensorProduct.productMap ψa ψb).toRingHom l hu hQ heq
      (kw_trp_pt W (X₃).functionField x₁ x₂ O) hs
    exact kw_trp_generic_ne_zeroPt W p₃ rfl (kw_trp_pt W (E).functionField OE OE ηE)
      (kw_trp_pt_pr₃ W _ OE OE ηE)
      (heq.symm.trans (hres.trans (kw_trp_pt_pr₃ W _ x₁ x₂ O)))
  ·
    intro h
    have hQ := kw_trp_pair_fac W (X₃).functionField ((X₃).fromSpecStalk (genericPoint X₃) ≫ kw_trp_q₂₃ W) ib ic ψb ψc
      ((Category.assoc _ _ _).trans ((congrArg ((X₃).fromSpecStalk (genericPoint X₃) ≫ ·) (kw_trp_q₂₃_fst W)).trans hb))
      ((Category.assoc _ _ _).trans ((congrArg ((X₃).fromSpecStalk (genericPoint X₃) ≫ ·) (kw_trp_q₂₃_snd W)).trans hc))
    have hgen : ((X₃).fromSpecStalk (genericPoint X₃) ≫ kw_trp_q₂₃ W) (IsLocalRing.closedPoint _)
        = genericPoint (pullback π π : Scheme.{u}) := by
      rw [Scheme.Hom.comp_apply]
      exact (congrArg (kw_trp_q₂₃ W)
        (Scheme.fromSpecStalk_closedPoint (x := genericPoint X₃))).trans
        (kw_trp_apply_genericPoint _ (kw_trp_q₂₃_surjective W))
    haveI : IsDomain ((𝒜 ib) ⊗[R] (𝒜 ic)) := isDomain_chartTensor_of_isElliptic W ib ic
    have hinj : Function.Injective (Algebra.TensorProduct.productMap ψb ψc).toRingHom :=
      kw_trp_injective_of_fac ((X₃).fromSpecStalk (genericPoint X₃) ≫ kw_trp_q₂₃ W) hgen
        ((chartIso ib ic).inv ≫ (C9).f (ib, ic)) _ hQ.symm
    refine (exists_lrSixU_ne_zero_of_isElliptic W ib ic).elim fun l hl0 => ?_
    have hu : IsUnit ((Algebra.TensorProduct.productMap ψb ψc) (kw_lrSixU W ib ic l)) :=
      isUnit_iff_ne_zero.mpr fun h0 => hl0 (hinj (h0.trans (map_zero _).symm))
    have hz := kw_lrApt_sixU_class_eq_addMap W (X₃).functionField hΔK ib ic ψb ψc l hu
    have heq := congrArg Subtype.val
      (kw_lrApt_toPointClass_injective W _ (hca.trans (h.trans hz.symm)))
    have hs : kw_trp_pt W (X₃).functionField O x₂ x₃ ≫ kw_trp_q₂₃ W
        = (X₃).fromSpecStalk (genericPoint X₃) ≫ kw_trp_q₂₃ W :=
      pullback.hom_ext
        ((Category.assoc _ _ _).trans
          ((congrArg (kw_trp_pt W (X₃).functionField O x₂ x₃ ≫ ·) (kw_trp_q₂₃_fst W)).trans
            ((kw_trp_pt_pr₂ W _ O x₂ x₃).trans
              ((congrArg ((X₃).fromSpecStalk (genericPoint X₃) ≫ ·) (kw_trp_q₂₃_fst W)).symm.trans
                (Category.assoc _ _ _).symm))))
        ((Category.assoc _ _ _).trans
          ((congrArg (kw_trp_pt W (X₃).functionField O x₂ x₃ ≫ ·) (kw_trp_q₂₃_snd W)).trans
            ((kw_trp_pt_pr₃ W _ O x₂ x₃).trans
              ((congrArg ((X₃).fromSpecStalk (genericPoint X₃) ≫ ·) (kw_trp_q₂₃_snd W)).symm.trans
                (Category.assoc _ _ _).symm))))
    have hres := kw_trp_restrict W (kw_trp_q₂₃ W) (p₁₂ ≫ pullback.fst π π) ib ic
      (Algebra.TensorProduct.productMap ψb ψc).toRingHom l hu hQ heq.symm
      (kw_trp_pt W (X₃).functionField O x₂ x₃) hs
    exact kw_trp_generic_ne_zeroPt W (p₁₂ ≫ pullback.fst π π) (kw_trp_pr₁_over W)
      (kw_trp_pt W (E).functionField ηE OE OE) (kw_trp_pt_pr₁ W _ ηE OE OE)
      (heq.trans (hres.trans (kw_trp_pt_pr₁ W _ O x₂ x₃)))

end Main
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.WeierstrassProjModel"
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option maxHeartbeats 6400000 in
theorem solution
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    haveI : Smooth (projModelStrCR W.toProjective) :=
      (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
    haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
      kw_hgi_geometricallyIntegral_of_baseChangeIso W
        (projModel_pullback_iso_baseChange W.toProjective)
    let X3 : Scheme.{u} :=
      pullback (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
    haveI : IsIntegral X3 := by
      haveI : IsLocallyNoetherian (projModelCR W.toProjective) :=
        LocallyOfFiniteType.isLocallyNoetherian (projModelStrCR W.toProjective)
      haveI : IsIntegral (projModelCR W.toProjective) :=
        GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
      haveI : GeometricallyIntegral (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
      haveI : IsIntegral ↑(pullback (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
          (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
      haveI : IsLocallyNoetherian ↑(pullback (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
      haveI : GeometricallyIntegral (pullback.fst (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
      exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
        (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
    letI : Algebra R X3.functionField :=
      (Spec.preimage (X3.fromSpecStalk (genericPoint X3)
        ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective)).hom.toAlgebra
    have hΔF : algebraMap R X3.functionField W.Δ ≠ 0 := (W.isUnit_Δ.map _).ne_zero
    ∃ (ia : Fin 3) (ψa : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ia : MvPolynomial (Fin 3) R)) →ₐ[R] X3.functionField)
      (ib : Fin 3) (ψb : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ib : MvPolynomial (Fin 3) R)) →ₐ[R] X3.functionField)
      (ic : Fin 3) (ψc : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ic : MvPolynomial (Fin 3) R)) →ₐ[R] X3.functionField),
      (X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψa.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ia)
      ∧ (X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψb.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ib)
      ∧ (X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψc.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ic)
      ∧ ((⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧
            : WeierstrassCurve.Projective.PointClass X3.functionField)
          ≠ ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧)
      ∧ ((⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧
            : WeierstrassCurve.Projective.PointClass X3.functionField)
          ≠ ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧)
      ∧ ((kw_lrApt_WF W X3.functionField).addMap
            ⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧
            ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧
          ≠ ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧)
      ∧ ((⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧
            : WeierstrassCurve.Projective.PointClass X3.functionField)
          ≠ (kw_lrApt_WF W X3.functionField).addMap
              ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧
              ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧) := by
  exact WeierstrassProjModel.kw_ev_trp_main W

end S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep
end P2MW
export P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep (solution)
