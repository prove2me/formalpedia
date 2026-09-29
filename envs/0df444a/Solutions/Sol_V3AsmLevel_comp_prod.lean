-- Prove2me | solution 1 for V3AsmLevel.comp_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4215d5e3-1561-548f-b133-aceb3aace20f

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSiteLevel
import Theorems.Thm_V3Glue_ChartInput_comap_iotaY_compG_chainPosPrime_eq
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_comap_iota_vanishingIdeal_closure_lines
import Theorems.Thm_ModularCurve_DRModelPackageLevel_range_comp_bcMap_eq_closure_and_isClosed
import Theorems.Thm_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal
import Theorems.Thm_V3Glue_ChartInput_prod_compG_comap_iotaY_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_prod_pow_eq_ofIdealTop_uSec_and_vSec_and_tSec
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_exists_idealSheafData_chartTable
import Theorems.Thm_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_crossingPt
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isRadical_span_natCast_sections_XO
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_eq_crossingPt_of_mem_closure_of_mem_closure
import Theorems.Thm_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_or
import Theorems.Thm_ModularCurve_DRLevel_bcMap_apply_notMem_preimage_basicOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3AsmLevel_comp_prod
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul
set_option maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3AsmLevel_comp_prod.AlgebraicGeometry"

universe u

section Model
open TopologicalSpace

namespace E9CP
namespace Model
open MvPolynomial MvPolynomial.CrossingQuotient MvPolynomial.CrossingQuotient.Resolution

variable {W : Type u} [CommRing W] (t : W) (e : ℕ)

private def lineSet (k : ℕ) : Set (Resolution t e) :=
  (⋃ (j : Fin e) (_ : (j : ℕ) + 1 = k), (Resolution.ι t e j) '' (PrimeSpectrum.zeroLocus {U t})) ∪
  (⋃ (j : Fin e) (_ : (j : ℕ) = k), (Resolution.ι t e j) '' (PrimeSpectrum.zeroLocus {V t}))

private theorem eq_of_comap_ι_eq' {I J : (Resolution t e).IdealSheafData} (h : ∀ i, I.comap (ι t e i) = J.comap (ι t e i)) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun i : Fin e => ⟨ι t e i ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion (ι t e i)⟩) ?_ ?_
  · simp only [Scheme.Hom.image_top_eq_opensRange]; exact iSup_opensRange_ι t e
  · intro i
    have hi := congrArg (fun K : (chartScheme t).IdealSheafData => K.ideal ⟨⊤, isAffineOpen_top _⟩) (h i)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hi
    exact Ideal.comap_injective_of_surjective _ ((ι t e i).appIso ⊤).commRingCatIsoToRingEquiv.symm.surjective hi

private theorem zeroLocus_U_eq : PrimeSpectrum.zeroLocus {U t} = {Q : chartScheme t | lineUIdeal t (Ideal.span {t}) (mem_span_t t) ≤ Q.asIdeal} := by
  ext Q
  rw [lineUIdeal_span_eq, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  show U t ∈ Q.asIdeal ↔ Ideal.span {U t} ≤ Q.asIdeal
  rw [Ideal.span_singleton_le_iff_mem]

private theorem zeroLocus_V_eq : PrimeSpectrum.zeroLocus {V t} = {Q : chartScheme t | lineVIdeal t (Ideal.span {t}) (mem_span_t t) ≤ Q.asIdeal} := by
  ext Q
  rw [lineVIdeal_span_eq, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  show V t ∈ Q.asIdeal ↔ Ideal.span {V t} ≤ Q.asIdeal
  rw [Ideal.span_singleton_le_iff_mem]

private theorem lineSet_eq_closure_lineGen [(Ideal.span {t} : Ideal W).IsMaximal] (k : Fin e) :
    lineSet t e k = closure {lineGen t e (Ideal.span {t}) (mem_span_t t) k} := by
  ext z
  rw [mem_closure_lineGen_iff, lineSet]
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_image, zeroLocus_U_eq, zeroLocus_V_eq, Set.mem_setOf_eq]
  constructor
  · rintro (⟨j, hj, Q, hQ, rfl⟩ | ⟨j, hj, Q, hQ, rfl⟩)
    · exact Or.inr ⟨j, Q, hj, hQ, rfl⟩
    · have : j = k := Fin.ext hj
      subst this
      exact Or.inl ⟨Q, hQ, rfl⟩
  · rintro (⟨Q, hQ, rfl⟩ | ⟨i, Q, hi, hQ, rfl⟩)
    · exact Or.inr ⟨k, rfl, Q, hQ, rfl⟩
    · exact Or.inl ⟨i, hi, Q, hQ, rfl⟩

private theorem lineSet_last_eq_closure_lineUGen [(Ideal.span {t} : Ideal W).IsMaximal] (i : Fin e) (hi : (i : ℕ) + 1 = e) :
    lineSet t e e = closure {lineUGen t e (Ideal.span {t}) (mem_span_t t) i} := by
  ext z
  rw [mem_closure_lineUGen_last_iff _ _ _ _ i hi, lineSet]
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_image, zeroLocus_U_eq, zeroLocus_V_eq, Set.mem_setOf_eq]
  constructor
  · rintro (⟨j, hj, Q, hQ, rfl⟩ | ⟨j, hj, Q, hQ, rfl⟩)
    · have : j = i := Fin.ext (by omega)
      subst this
      exact ⟨Q, hQ, rfl⟩
    · exact absurd hj (by have := j.2; omega)
  · rintro ⟨Q, hQ, rfl⟩
    exact Or.inl ⟨i, hi, Q, hQ, rfl⟩

variable (F : Fin (e + 1) → (Resolution t e).IdealSheafData)
  (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι t e i) =
    Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
      (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)))
include hF

private theorem eq_vanishingIdeal_closure_lineSet [IsReduced (W ⧸ Ideal.span {t})] (k : Fin (e + 1)) :
    F k = Scheme.IdealSheafData.vanishingIdeal ⟨closure (lineSet t e k), isClosed_closure⟩ := by
  apply eq_of_comap_ι_eq'
  intro i
  rw [hF i k]
  exact (comap_iota_vanishingIdeal_closure_lines t e i (k : ℕ)).symm

private theorem eq_vanishingIdeal_closure_lineGen [IsReduced (W ⧸ Ideal.span {t})] [(Ideal.span {t} : Ideal W).IsMaximal] (k : Fin e) :
    F ⟨k, by omega⟩ = Scheme.IdealSheafData.vanishingIdeal ⟨closure {lineGen t e (Ideal.span {t}) (mem_span_t t) k}, isClosed_closure⟩ := by
  rw [eq_vanishingIdeal_closure_lineSet t e F hF]
  congr 2
  rw [show ((⟨k, by omega⟩ : Fin (e + 1)) : ℕ) = (k : ℕ) from rfl, lineSet_eq_closure_lineGen, closure_closure]

private theorem eq_vanishingIdeal_closure_lineUGen_last [IsReduced (W ⧸ Ideal.span {t})] [(Ideal.span {t} : Ideal W).IsMaximal]
    (i : Fin e) (hi : (i : ℕ) + 1 = e) :
    F (Fin.last e) = Scheme.IdealSheafData.vanishingIdeal ⟨closure {lineUGen t e (Ideal.span {t}) (mem_span_t t) i}, isClosed_closure⟩ := by
  rw [eq_vanishingIdeal_closure_lineSet t e F hF]
  congr 2
  rw [Fin.val_last, lineSet_last_eq_closure_lineUGen t e i hi, closure_closure]

end E9CP.Model

private theorem E9CP.Model.lineUGen_congr_ideal {W : Type u} [CommRing W] (t : W) (e : ℕ) {𝔭 𝔭' : Ideal W} [𝔭.IsPrime] [𝔭'.IsPrime]
    (ht : t ∈ 𝔭) (ht' : t ∈ 𝔭') (h : 𝔭 = 𝔭') (k : Fin e) :
    MvPolynomial.CrossingQuotient.Resolution.lineUGen t e 𝔭 ht k = MvPolynomial.CrossingQuotient.Resolution.lineUGen t e 𝔭' ht' k := by
  subst h; rfl

private theorem E9CP.Model.lineGen_congr_ideal {W : Type u} [CommRing W] (t : W) (e : ℕ) {𝔭 𝔭' : Ideal W} [𝔭.IsPrime] [𝔭'.IsPrime]
    (ht : t ∈ 𝔭) (ht' : t ∈ 𝔭') (h : 𝔭 = 𝔭') (k : Fin e) :
    MvPolynomial.CrossingQuotient.Resolution.lineGen t e 𝔭 ht k = MvPolynomial.CrossingQuotient.Resolution.lineGen t e 𝔭' ht' k := by
  subst h; rfl

end Model

section L3
open TopologicalSpace Opposite

namespace E9CP
namespace L3gen

private theorem isReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced X := by

  suffices h : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) by
    haveI := h; exact isReduced_of_isReduced_stalk X
  intro x
  obtain ⟨U, hU, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨U', hU'aff, rfl⟩ := hU
  have hxV0 : x ∈ (f ⁻¹ᵁ U' : X.Opens) := hxU
  obtain ⟨V, hV, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV0 (f ⁻¹ᵁ U').2
  obtain ⟨V', hV'aff, rfl⟩ := hV

  have het : (f.appLE U' V' hVU).hom.Etale := Etale.etale_appLE f hU'aff hV'aff hVU
  letI := (f.appLE U' V' hVU).hom.toAlgebra
  haveI : Algebra.Etale Γ(Y, U') Γ(X, V') := het
  haveI : IsNoetherianRing Γ(Y, U') := IsLocallyNoetherian.component_noetherian ⟨U', hU'aff⟩
  haveI : _root_.IsReduced Γ(Y, U') := IsReduced.component_reduced _
  have hredV : _root_.IsReduced Γ(X, V') := Algebra.Smooth.isReduced_of_isReduced_of_isNoetherianRing Γ(Y, U') Γ(X, V')

  haveI : IsAffine (V' : Scheme.{u}) := hV'aff

  letI : Algebra Γ(X, V') (X.presheaf.stalk ((⟨x, hxV⟩ : V') : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V')
  haveI := hV'aff.isLocalization_stalk ⟨x, hxV⟩
  exact isReduced_localizationPreserves (hV'aff.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk ((⟨x, hxV⟩ : V') : X)) hredV

end E9CP.L3gen

end L3

section L4ws4

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3AsmLevel_comp_prod.AlgebraicGeometry"

namespace E9CP
namespace L4
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

section Unramified

open IsLocalRing

private theorem eq_of_specializes_of_apply_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    {x x' : X} (h : x' ⤳ x) (hf : f.base x' = f.base x) : x' = x := by

  have hx' : x' ∈ Set.range (X.fromSpecStalk x).base := by rw [Scheme.range_fromSpecStalk]; exact h
  obtain ⟨q, hq⟩ := hx'

  have himg : (Spec.map (f.stalkMap x)).base q = closedPoint (Y.presheaf.stalk (f.base x)) := by
    apply (Y.fromSpecStalk (f.base x)).isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.Hom.comp_apply, hq, hf,
      Scheme.fromSpecStalk_closedPoint]

  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  have hmap := Algebra.FormallyUnramified.map_maximalIdeal (R := Y.presheaf.stalk (f.base x)) (S := X.presheaf.stalk x)

  have hcomap : q.asIdeal.comap (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) =
      maximalIdeal (Y.presheaf.stalk (f.base x)) := by
    have := congrArg PrimeSpectrum.asIdeal himg
    exact this
  have hle : maximalIdeal (X.presheaf.stalk x) ≤ q.asIdeal := by
    rw [← hmap, Ideal.map_le_iff_le_comap, hcomap]
  have hq' : q = closedPoint (X.presheaf.stalk x) := by
    apply PrimeSpectrum.ext
    exact ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le q.isPrime.ne_top hle).symm
  rw [← hq, hq', Scheme.fromSpecStalk_closedPoint]

end Unramified
end E9CP.L4

namespace E9CP
namespace L4
section ModelD
p2m_open "MvPolynomial.CrossingQuotient Polynomial AlgebraicGeometry.Polynomial"

variable {W : Type u} [CommRing W] (s : W) (𝔭 : Ideal W) [𝔭.IsMaximal] (hs : s ∈ 𝔭)

private theorem lineVHom_surjective' : Function.Surjective (lineVHom s 𝔭 hs) := by
  intro q
  induction q using Polynomial.induction_on with
  | C a =>
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨algebraMap W _ w, ?_⟩
    rw [AlgHom.commutes, Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp; obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | monomial n a h =>
    obtain ⟨c, hc⟩ := h
    refine ⟨c * U s, ?_⟩
    rw [map_mul, hc, lineVHom_U, pow_succ, mul_assoc]

private theorem lineUHom_surjective' : Function.Surjective (lineUHom s 𝔭 hs) := by
  intro q
  induction q using Polynomial.induction_on with
  | C a =>
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨algebraMap W _ w, ?_⟩
    rw [AlgHom.commutes, Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp; obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | monomial n a h =>
    obtain ⟨c, hc⟩ := h
    refine ⟨c * V s, ?_⟩
    rw [map_mul, hc, lineUHom_V, pow_succ, mul_assoc]

private theorem eq_bot_of_le_span_X {k : Type*} [Field k] {Q : Ideal k[X]} [Q.IsPrime] (hle : Q ≤ Ideal.span {(X : k[X])})
    (hX : (X : k[X]) ∉ Q) : Q = ⊥ := by
  by_contra hne
  have hmax : Q.IsMaximal := IsPrime.to_maximal_ideal hne
  have hXtop : Ideal.span {(X : k[X])} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact Polynomial.not_isUnit_X
  have := hmax.eq_of_le hXtop hle
  exact hX (this ▸ Ideal.mem_span_singleton_self _)

private theorem eq_lineVIdeal_of_le {P : Ideal (MvPolynomial.CrossingQuotient W s)} [P.IsPrime]
    (h1 : lineVIdeal s 𝔭 hs ≤ P) (h2 : P ≤ originIdeal s 𝔭 hs) (hU : U s ∉ P) : P = lineVIdeal s 𝔭 hs := by
  letI := Ideal.Quotient.field 𝔭
  have hsurj := lineVHom_surjective' s 𝔭 hs
  have hker : RingHom.ker (lineVHom s 𝔭 hs).toRingHom ≤ P := h1
  set Q : Ideal (W ⧸ 𝔭)[X] := P.map (lineVHom s 𝔭 hs).toRingHom with hQ
  haveI : Q.IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  have hXQ : (X : (W ⧸ 𝔭)[X]) ∉ Q := by
    intro hX
    rw [hQ, Ideal.mem_map_iff_of_surjective (lineVHom s 𝔭 hs).toRingHom hsurj] at hX
    obtain ⟨c, hc, hcX⟩ := hX
    apply hU
    have hmem : c - U s ∈ lineVIdeal s 𝔭 hs := by
      rw [mem_lineVIdeal_iff, map_sub, lineVHom_U]
      change (lineVHom s 𝔭 hs).toRingHom c - X = 0
      rw [hcX, sub_self]
    have := h1 hmem
    simpa using P.sub_mem hc this
  have hQle : Q ≤ Ideal.span {(X : (W ⧸ 𝔭)[X])} := by
    intro q hq
    rw [hQ, Ideal.mem_map_iff_of_surjective (lineVHom s 𝔭 hs).toRingHom hsurj] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    have h0 : (Polynomial.aeval (0 : W ⧸ 𝔭)) ((lineVHom s 𝔭 hs) c) = 0 := by
      have := congrArg (fun f => f c) (aeval_zero_comp_lineVHom s 𝔭 hs)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      rw [this]
      exact (mem_originIdeal_iff s 𝔭 hs c).mp (h2 hc)
    rw [Polynomial.coe_aeval_eq_eval, ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.X_dvd_iff] at h0
    exact Ideal.mem_span_singleton.mpr h0
  have hQbot : Q = ⊥ := eq_bot_of_le_span_X hQle hXQ
  apply le_antisymm _ h1
  calc P ≤ Ideal.comap (lineVHom s 𝔭 hs).toRingHom Q := Ideal.le_comap_map
    _ = lineVIdeal s 𝔭 hs := by rw [hQbot, ← RingHom.ker_eq_comap_bot]; rfl

private theorem eq_lineUIdeal_of_le {P : Ideal (MvPolynomial.CrossingQuotient W s)} [P.IsPrime]
    (h1 : lineUIdeal s 𝔭 hs ≤ P) (h2 : P ≤ originIdeal s 𝔭 hs) (hV : V s ∉ P) : P = lineUIdeal s 𝔭 hs := by
  letI := Ideal.Quotient.field 𝔭
  have hsurj := lineUHom_surjective' s 𝔭 hs
  have hker : RingHom.ker (lineUHom s 𝔭 hs).toRingHom ≤ P := h1
  set Q : Ideal (W ⧸ 𝔭)[X] := P.map (lineUHom s 𝔭 hs).toRingHom with hQ
  haveI : Q.IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  have hXQ : (X : (W ⧸ 𝔭)[X]) ∉ Q := by
    intro hX
    rw [hQ, Ideal.mem_map_iff_of_surjective (lineUHom s 𝔭 hs).toRingHom hsurj] at hX
    obtain ⟨c, hc, hcX⟩ := hX
    apply hV
    have hmem : c - V s ∈ lineUIdeal s 𝔭 hs := by
      rw [mem_lineUIdeal_iff, map_sub, lineUHom_V]
      change (lineUHom s 𝔭 hs).toRingHom c - X = 0
      rw [hcX, sub_self]
    have := h1 hmem
    simpa using P.sub_mem hc this
  have hQle : Q ≤ Ideal.span {(X : (W ⧸ 𝔭)[X])} := by
    intro q hq
    rw [hQ, Ideal.mem_map_iff_of_surjective (lineUHom s 𝔭 hs).toRingHom hsurj] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    have h0 : (Polynomial.aeval (0 : W ⧸ 𝔭)) ((lineUHom s 𝔭 hs) c) = 0 := by
      have := congrArg (fun f => f c) (aeval_zero_comp_lineUHom s 𝔭 hs)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      rw [this]
      exact (mem_originIdeal_iff s 𝔭 hs c).mp (h2 hc)
    rw [Polynomial.coe_aeval_eq_eval, ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.X_dvd_iff] at h0
    exact Ideal.mem_span_singleton.mpr h0
  have hQbot : Q = ⊥ := eq_bot_of_le_span_X hQle hXQ
  apply le_antisymm _ h1
  calc P ≤ Ideal.comap (lineUHom s 𝔭 hs).toRingHom Q := Ideal.le_comap_map
    _ = lineUIdeal s 𝔭 hs := by rw [hQbot, ← RingHom.ker_eq_comap_bot]; rfl

end ModelD
end E9CP.L4

namespace E9CP
namespace L4
section Site
open ModularCurve MvPolynomial.CrossingQuotient MvPolynomial.CrossingQuotient.Resolution Topology

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ) (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ)

local notation "CC" => V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H

private theorem ξ_specializes_x (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (j : Fin 2) : V3AsmLevel.ξ 𝔛 O ρO κ toκ j ⤳ (CC).x n := by
  have h := ModularCurve.DRModelPackageLevel.bcMap_genericPoint_specializes_crossingPt N₀ q hqN 𝔛 O ρO κ toκ n
  change V3AsmLevel.ξ 𝔛 O ρO κ toκ j ⤳ V3Glue.LevelSite.xpt 𝔛 (V3AsmLevel.bc O ρO κ toκ) n
  revert j
  refine Fin.cases ?_ (fun i => ?_)
  · exact h.1
  · have : i = 0 := Subsingleton.elim _ _
    subst this
    exact h.2

private theorem ξ_specializes_xU (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (j : Fin 2) (hU : V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (CC).U n) :
    (⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU⟩ : ↥((CC).U n)) ⤳ (CC).xU n :=
  Topology.IsInducing.subtypeVal.specializes_iff.mp (ξ_specializes_x 𝔛 O ρO hϖ κ toκ H n j)

private theorem ξ_ne_x (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (CC).X0) (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (j : Fin 2) :
    V3AsmLevel.ξ 𝔛 O ρO κ toκ j ≠ (CC).x n :=
  (V3AsmLevel.mem_X0_iff 𝔛 O ρO κ toκ hϖ H _).mp (hξ j) n

private theorem V_mem_f (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : ↥((CC).U n))
    (hy : (y : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0 ≫ V3AsmLevel.bc O ρO κ toκ).base) :
    V (((q : ℕ) : O) ^ (CC).thick n) ∈ (((CC).f n).base y).asIdeal := by
  have key := (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).orient_inf_conv
  refine key _ ?_
  convert hy using 2
  exact congrArg (fun φ => φ.base y) (Scheme.homOfLE_ι _ _)

private theorem U_mem_f (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : ↥((CC).U n))
    (hy : (y : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1 ≫ V3AsmLevel.bc O ρO κ toκ).base) :
    U (((q : ℕ) : O) ^ (CC).thick n) ∈ (((CC).f n).base y).asIdeal := by
  have key := (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).orient_zero_conv
  refine key _ ?_
  convert hy using 2
  exact congrArg (fun φ => φ.base y) (Scheme.homOfLE_ι _ _)

private theorem mem_range_compInf_of_V_mem (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : ↥((CC).U n))
    (hV : V (((q : ℕ) : O) ^ (CC).thick n) ∈ (((CC).f n).base y).asIdeal) :
    (y : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0 ≫ V3AsmLevel.bc O ρO κ toκ).base := by
  have key := (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).orient_inf _ hV
  convert key using 2
  exact (congrArg (fun φ => φ.base y) (Scheme.homOfLE_ι _ _)).symm

private theorem mem_range_compZero_of_U_mem (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : ↥((CC).U n))
    (hU : U (((q : ℕ) : O) ^ (CC).thick n) ∈ (((CC).f n).base y).asIdeal) :
    (y : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1 ≫ V3AsmLevel.bc O ρO κ toκ).base := by
  have key := (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).orient_zero _ hU
  convert key using 2
  exact (congrArg (fun φ => φ.base y) (Scheme.homOfLE_ι _ _)).symm

private theorem not_U_mem_and_V_mem (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : ↥((CC).U n)) (hy : (y : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ≠ (CC).x n) :
    ¬ (U (((q : ℕ) : O) ^ (CC).thick n) ∈ (((CC).f n).base y).asIdeal ∧
       V (((q : ℕ) : O) ^ (CC).thick n) ∈ (((CC).f n).base y).asIdeal) := by
  have h := ((CC).f_mem_Vc_iff n y).mpr hy
  rcases TopologicalSpace.Opens.mem_sup.mp h with hU | hV
  · exact fun hh => (PrimeSpectrum.mem_basicOpen _ _).mp hU hh.1
  · exact fun hh => (PrimeSpectrum.mem_basicOpen _ _).mp hV hh.2

private theorem forall_algebraMap_mem (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (P : crossingScheme (((q : ℕ) : O) ^ (CC).thick n))
    (h : U (((q : ℕ) : O) ^ (CC).thick n) ∈ P.asIdeal ∨ V (((q : ℕ) : O) ^ (CC).thick n) ∈ P.asIdeal) :
    ∀ w ∈ IsLocalRing.maximalIdeal O, algebraMap O (MvPolynomial.CrossingQuotient O (((q : ℕ) : O) ^ (CC).thick n)) w ∈ P.asIdeal := by
  have he := (CC).one_le_thick n
  have hpe : algebraMap O (MvPolynomial.CrossingQuotient O (((q : ℕ) : O) ^ (CC).thick n)) (((q : ℕ) : O) ^ (CC).thick n) ∈ P.asIdeal := by
    rw [← U_mul_V]
    rcases h with h | h
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h
  have hpe' : (algebraMap O (MvPolynomial.CrossingQuotient O (((q : ℕ) : O) ^ (CC).thick n)) ((q : ℕ) : O)) ^ (CC).thick n ∈ P.asIdeal := by
    rw [← map_pow]; exact hpe
  have hp := P.isPrime.mem_of_pow_mem _ hpe'
  intro w hw
  rw [hϖ] at hw
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
  rw [map_mul]; exact Ideal.mul_mem_left _ _ hp

private theorem f_ξ_zero (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (CC).X0) (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO))
    (hU : V3AsmLevel.ξ 𝔛 O ρO κ toκ 0 ∈ (CC).U n) :
    ((CC).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hU⟩ =
      branchVPt ((q : ℕ) : O) ((CC).thick n) (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) ((CC).one_le_thick n) := by
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  set P := ((CC).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hU⟩ with hP
  have hV : V (((q : ℕ) : O) ^ (CC).thick n) ∈ P.asIdeal :=
    V_mem_f 𝔛 O ρO hϖ κ toκ H n _ ⟨genericPoint _, by show _ = V3AsmLevel.ξ 𝔛 O ρO κ toκ 0; rw [V3AsmLevel.ξ_zero]⟩
  have hUn : U (((q : ℕ) : O) ^ (CC).thick n) ∉ P.asIdeal := fun h =>
    not_U_mem_and_V_mem 𝔛 O ρO hϖ κ toκ H n _ (ξ_ne_x 𝔛 O ρO hϖ κ toκ H hξ n 0) ⟨h, hV⟩
  have h1 : lineVIdeal (((q : ℕ) : O) ^ (CC).thick n) (IsLocalRing.maximalIdeal O)
      (t_pow_mem ((q : ℕ) : O) _ (V3AsmLevel.p_mem_maximalIdeal O hϖ) _ ((CC).one_le_thick n)) ≤ P.asIdeal :=
    (lineVIdeal_le_iff _ _ _).mpr ⟨hV, forall_algebraMap_mem 𝔛 O ρO hϖ κ toκ H n P (Or.inr hV)⟩
  have hspec : P ⤳ (CC).vertex n := by
    rw [hP, (CC).vertex_def]
    exact (ξ_specializes_xU 𝔛 O ρO hϖ κ toκ H n 0 hU).map ((CC).f n).continuous
  rw [V3AsmLevel.vertex_eq] at hspec
  have h2 : P.asIdeal ≤ vertexIdeal ((q : ℕ) : O) (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ)
      ((CC).thick n) ((CC).one_le_thick n) :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr hspec
  apply PrimeSpectrum.ext
  haveI := P.isPrime
  exact eq_lineVIdeal_of_le _ _ _ h1 h2 hUn

private theorem f_ξ_one (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (CC).X0) (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO))
    (hU : V3AsmLevel.ξ 𝔛 O ρO κ toκ 1 ∈ (CC).U n) :
    ((CC).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hU⟩ =
      branchUPt ((q : ℕ) : O) ((CC).thick n) (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) ((CC).one_le_thick n) := by
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  set P := ((CC).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hU⟩ with hP
  have hUm : U (((q : ℕ) : O) ^ (CC).thick n) ∈ P.asIdeal :=
    U_mem_f 𝔛 O ρO hϖ κ toκ H n _ ⟨genericPoint _, by show _ = V3AsmLevel.ξ 𝔛 O ρO κ toκ 1; rw [V3AsmLevel.ξ_one]⟩
  have hVn : V (((q : ℕ) : O) ^ (CC).thick n) ∉ P.asIdeal := fun h =>
    not_U_mem_and_V_mem 𝔛 O ρO hϖ κ toκ H n _ (ξ_ne_x 𝔛 O ρO hϖ κ toκ H hξ n 1) ⟨hUm, h⟩
  have h1 : lineUIdeal (((q : ℕ) : O) ^ (CC).thick n) (IsLocalRing.maximalIdeal O)
      (t_pow_mem ((q : ℕ) : O) _ (V3AsmLevel.p_mem_maximalIdeal O hϖ) _ ((CC).one_le_thick n)) ≤ P.asIdeal :=
    (lineUIdeal_le_iff _ _ _).mpr ⟨hUm, forall_algebraMap_mem 𝔛 O ρO hϖ κ toκ H n P (Or.inl hUm)⟩
  have hspec : P ⤳ (CC).vertex n := by
    rw [hP, (CC).vertex_def]
    exact (ξ_specializes_xU 𝔛 O ρO hϖ κ toκ H n 1 hU).map ((CC).f n).continuous
  rw [V3AsmLevel.vertex_eq] at hspec
  have h2 : P.asIdeal ≤ vertexIdeal ((q : ℕ) : O) (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ)
      ((CC).thick n) ((CC).one_le_thick n) :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr hspec
  apply PrimeSpectrum.ext
  haveI := P.isPrime
  exact eq_lineUIdeal_of_le _ _ _ h1 h2 hVn

private theorem ρ_injOn (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) {z₁ z₂ : (CC).Res n} (h1 : ((CC).ρ n).base z₁ ∈ (CC).Vc n)
    (h : ((CC).ρ n).base z₁ = ((CC).ρ n).base z₂) : z₁ = z₂ := by
  have h2 : ((CC).ρ n).base z₂ ∈ (CC).Vc n := h ▸ h1
  have key : ((CC).ρ n ∣_ (CC).Vc n).base ⟨z₁, h1⟩ = ((CC).ρ n ∣_ (CC).Vc n).base ⟨z₂, h2⟩ := by
    apply Subtype.ext
    rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
    exact h
  have hinj := ((CC).ρ n ∣_ (CC).Vc n).isOpenEmbedding.injective
  exact congrArg Subtype.val (hinj key)

private theorem ρ_g_apply (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : (CC).Y n) : ((CC).ρ n).base (((CC).g n).base y) = ((CC).f n).base (((CC).q n).base y) := by
  have := congrArg (fun φ => φ.base y) ((CC).q_f n)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
  exact this.symm

private theorem q_j_coe (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (z : ↥((CC).U n ⊓ (CC).X0)) :
    (((CC).q n).base (((CC).j n).base z)).1 = z.1 := by
  have := congrArg (fun φ => φ.base z) ((CC).j_q n)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
  rw [this]
  exact congrArg (fun φ => φ.base z) ((ModularCurve.DRLevel.XO (N₀ := N₀) ρO).homOfLE_ι (inf_le_left : (CC).U n ⊓ (CC).X0 ≤ (CC).U n))

private scoped instance formallyUnramified_f (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) : FormallyUnramified ((CC).f n) :=
  ((Etale.iff_flat_and_formallyUnramified).mp ((CC).f_etale n)).2.1

end Site
end E9CP.L4
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP"

set_option maxHeartbeats 6400000 in

private theorem E9CP.Asm.preimage_g_lineGen_zero_and_lineUGen_last
    {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ) (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0)
    (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (hU : ∀ j : Fin 2, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n) :
    ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).g n).base ⁻¹'
        {MvPolynomial.CrossingQuotient.Resolution.lineGen ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)
          (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) ⟨0, (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).one_le_thick n⟩} =
      {(V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ξY (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ n 0 (hU 0)} ∧
    ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).g n).base ⁻¹'
        {MvPolynomial.CrossingQuotient.Resolution.lineUGen ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)
          (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ)
          ⟨(V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n - 1, by have := (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).one_le_thick n; omega⟩} =
      {(V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ξY (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ n 1 (hU 1)} := by
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)

  have he := (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).one_le_thick n
  have hf0 := E9CP.L4.f_ξ_zero 𝔛 O ρO hϖ κ toκ H hξ n (hU 0)
  have hf1 := E9CP.L4.f_ξ_one 𝔛 O ρO hϖ κ toκ H hξ n (hU 1)

  have hbV : MvPolynomial.CrossingQuotient.Resolution.branchVPt ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)
      (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) he ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Vc n := by
    apply TopologicalSpace.Opens.mem_sup.mpr; left
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr (MvPolynomial.CrossingQuotient.U_notMem_lineVIdeal _ _ _)
  have hbU : MvPolynomial.CrossingQuotient.Resolution.branchUPt ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)
      (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) he ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Vc n := by
    apply TopologicalSpace.Opens.mem_sup.mpr; right
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr (MvPolynomial.CrossingQuotient.V_notMem_lineUIdeal _ _ _)

  have main : ∀ (j : Fin 2) (L : (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Res n)
      (hL : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base L = ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU j⟩)
      (hLVc : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base L ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Vc n),
      ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).g n).base ⁻¹' {L} =
        {(V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ξY (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ n j (hU j)} := by
    intro j L hL hLVc
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy

      have hρ : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).q n).base y) =
          ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base L := by
        rw [← E9CP.L4.ρ_g_apply, hy]
      have hVc : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).q n).base y) ∈
          (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Vc n := hρ ▸ hLVc
      have hne : (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).q n).base y).1 ≠ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).x n :=
        ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f_mem_Vc_iff n _).mp hVc
      have hX0 : (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).q n).base y).1 ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0 := by
        rw [(V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).mem_X0]
        intro m hm
        by_cases hmn : m = n
        · subst hmn; exact hne hm
        · exact (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).x_not_mem_U n m hmn
            (hm ▸ (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).q n).base y).2)
      obtain ⟨z, hz⟩ := (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).hq n y hX0

      have hw : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).q n).base y = ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU j⟩ := by
        symm
        refine E9CP.L4.eq_of_specializes_of_apply_eq ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n) ?_ ?_
        ·
          apply Topology.IsInducing.subtypeVal.specializes_iff.mp
          change V3AsmLevel.ξ 𝔛 O ρO κ toκ j ⤳ _
          revert hρ
          revert L
          refine Fin.cases ?_ (fun i => ?_) j <;> intro L hL hLVc hy hρ
          · have hVm : MvPolynomial.CrossingQuotient.V (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∈
                (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).q n).base y)).asIdeal := by
              rw [hρ, hL, hf0]
              exact MvPolynomial.CrossingQuotient.V_mem_lineVIdeal _ _ _
            have hr := E9CP.L4.mem_range_compInf_of_V_mem 𝔛 O ρO hϖ κ toκ H n _ hVm
            rw [(ModularCurve.DRModelPackageLevel.range_comp_bcMap_eq_closure_and_isClosed N₀ q hqN 𝔛 O ρO hϖ κ toκ 0).1,
              ← V3AsmLevel.ξ_zero] at hr
            exact specializes_iff_mem_closure.mpr hr
          · obtain rfl : i = 0 := Subsingleton.elim _ _
            have hUm : MvPolynomial.CrossingQuotient.U (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∈
                (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).q n).base y)).asIdeal := by
              rw [hρ, hL]
              change _ ∈ (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hU 1⟩).asIdeal
              rw [hf1]
              exact MvPolynomial.CrossingQuotient.U_mem_lineUIdeal _ _ _
            have hr := E9CP.L4.mem_range_compZero_of_U_mem 𝔛 O ρO hϖ κ toκ H n _ hUm
            rw [(ModularCurve.DRModelPackageLevel.range_comp_bcMap_eq_closure_and_isClosed N₀ q hqN 𝔛 O ρO hϖ κ toκ 1).1]
              at hr
            have h1 : V3AsmLevel.ξ 𝔛 O ρO κ toκ 1 = (𝔛.comp κ (toκ.comp ρO) 1 ≫ ModularCurve.DRLevel.bcMap ρO toκ).base
                (genericPoint (ModularCurve.DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) := V3AsmLevel.ξ_one ..
            change V3AsmLevel.ξ 𝔛 O ρO κ toκ 1 ⤳ _
            rw [h1]
            exact specializes_iff_mem_closure.mpr hr
        · rw [hρ, hL]

      rw [← hz]
      change ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).j n).base z =
        ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).j n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU j, hξ j⟩
      congr 1
      apply Subtype.ext
      have h3 := E9CP.L4.q_j_coe 𝔛 O ρO hϖ κ toκ H n z
      rw [hz, hw] at h3
      exact h3.symm
    · intro hy
      subst hy
      apply E9CP.L4.ρ_injOn 𝔛 O ρO hϖ κ toκ H n ?_ ?_
      · rw [E9CP.L4.ρ_g_apply]
        change ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).q n).base
          (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).j n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU j, hξ j⟩)) ∈ _
        have h3 := E9CP.L4.q_j_coe 𝔛 O ρO hϖ κ toκ H n ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU j, hξ j⟩
        have h4 : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).q n).base (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).j n).base
            ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU j, hξ j⟩) = ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU j⟩ := Subtype.ext h3
        rw [h4, ← hL]; exact hLVc
      · rw [E9CP.L4.ρ_g_apply, hL]
        congr 1
        exact Subtype.ext (E9CP.L4.q_j_coe 𝔛 O ρO hϖ κ toκ H n ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU j, hξ j⟩)
  have hL0 : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base (MvPolynomial.CrossingQuotient.Resolution.lineGen ((q : ℕ) : O)
      ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) ⟨0, he⟩) =
      MvPolynomial.CrossingQuotient.Resolution.branchVPt ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)
        (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) he :=
    MvPolynomial.CrossingQuotient.Resolution.toCrossing_lineGen_zero _ _ _ _ _ rfl
  have hL1 : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base (MvPolynomial.CrossingQuotient.Resolution.lineUGen ((q : ℕ) : O)
      ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ)
      ⟨(V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n - 1, by omega⟩) =
      MvPolynomial.CrossingQuotient.Resolution.branchUPt ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)
        (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) he :=
    MvPolynomial.CrossingQuotient.Resolution.toCrossing_lineUGen_last _ _ _ _ _
      (by change (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n - 1 + 1 = (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n; omega)
  constructor
  · exact main 0 _ (by rw [hL0, hf0]) (by rw [hL0]; exact hbV)
  · exact main 1 _ (by rw [hL1, hf1]) (by rw [hL1]; exact hbU)

end L4ws4
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

namespace E9CP
namespace Asm

open ModularCurve MvPolynomial MvPolynomial.CrossingQuotient

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ) (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0)

private theorem comap_ιY_comp_eq
    (Fc : ∀ e : ℕ, Fin (e + 1) → (MvPolynomial.CrossingQuotient.Resolution ((q : ℕ) : O) e).IdealSheafData)
    (hF : ∀ (e : ℕ) (i : Fin e) (k : Fin (e + 1)), (Fc e k).comap (MvPolynomial.CrossingQuotient.Resolution.ι ((q : ℕ) : O) e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient O ((q : ℕ) : O)))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {MvPolynomial.CrossingQuotient.V ((q : ℕ) : O)}
          else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {MvPolynomial.CrossingQuotient.U ((q : ℕ) : O)} else ⊤)))
    (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (d : Fin ((V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n + 1)) :
    (V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n d)).comap
        ((V3AsmLevel.D 𝔛 O ρO κ toκ hϖ H).ιY n) =
      (Fc ((V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n) d).comap ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).g n) := by
  let C := V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H

  have hU : ∀ j : Fin 2, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ C.U n := by

    have hx : C.x n ∈ (C.U n : Set (ModularCurve.DRLevel.XO (N₀ := N₀) ρO)) := C.x_mem_U n
    have hx0 : C.x n ∈ closure {V3AsmLevel.ξ 𝔛 O ρO κ toκ 0} := by
      rw [V3AsmLevel.ξ_zero, ← (ModularCurve.DRModelPackageLevel.range_comp_bcMap_eq_closure_and_isClosed N₀ q hqN 𝔛 O ρO hϖ κ toκ 0).1]
      exact ⟨(pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n, rfl⟩
    have hx1 : C.x n ∈ closure {V3AsmLevel.ξ 𝔛 O ρO κ toκ 1} := by
      rw [V3AsmLevel.ξ_one, ← (ModularCurve.DRModelPackageLevel.range_comp_bcMap_eq_closure_and_isClosed N₀ q hqN 𝔛 O ρO hϖ κ toκ 1).1]
      refine ⟨(pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n, ?_⟩
      change ((pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)) ≫ 𝔛.comp κ (toκ.comp ρO) 1 ≫ ModularCurve.DRLevel.bcMap ρO toκ).base n =
        ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)) ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫ ModularCurve.DRLevel.bcMap ρO toκ).base n
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    intro j
    refine V3Glue.Aux.mem_of_closure_singleton_inter_nonempty (C.U n).2 ?_
    refine Fin.cases ⟨C.x n, hx0, hx⟩ (fun _ => ⟨C.x n, ?_, hx⟩) j
    (first | exact hx1 | simpa using hx1 | (have h__ := hx1; simp at h__; exact h__))

  haveI hmaxI : (Ideal.span {((q : ℕ) : O)} : Ideal O).IsMaximal := hϖ ▸ IsLocalRing.maximalIdeal.isMaximal O
  haveI hredI : IsReduced (O ⧸ (Ideal.span {((q : ℕ) : O)} : Ideal O)) := by
    letI := Ideal.Quotient.field (Ideal.span {((q : ℕ) : O)} : Ideal O); infer_instance
  have hFe := hF (C.thick n)
  have L1exc : ∀ k : Fin (C.thick n - 1), Fc (C.thick n) ⟨(k : ℕ) + 1, by omega⟩ =
      Scheme.IdealSheafData.vanishingIdeal ⟨closure {V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H n k}, isClosed_closure⟩ := by
    intro k
    have h := E9CP.Model.eq_vanishingIdeal_closure_lineGen ((q : ℕ) : O) (C.thick n)
      (Fc (C.thick n)) hFe ⟨(k : ℕ) + 1, by omega⟩
    rw [h]
    congr 3
    refine congrArg (fun z : C.Res n => ({z} : Set (C.Res n))) ?_
    symm
    calc V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H n k
        = MvPolynomial.CrossingQuotient.Resolution.lineUGen ((q : ℕ) : O) (C.thick n) (IsLocalRing.maximalIdeal O)
            (V3AsmLevel.p_mem_maximalIdeal O hϖ) ⟨(k : ℕ), by omega⟩ := rfl
      _ = MvPolynomial.CrossingQuotient.Resolution.lineUGen ((q : ℕ) : O) (C.thick n) (Ideal.span {((q : ℕ) : O)})
            (MvPolynomial.CrossingQuotient.mem_span_t _) ⟨(k : ℕ), by omega⟩ :=
          E9CP.Model.lineUGen_congr_ideal _ _ _ _ hϖ _
      _ = MvPolynomial.CrossingQuotient.Resolution.lineGen ((q : ℕ) : O) (C.thick n) (Ideal.span {((q : ℕ) : O)})
            (MvPolynomial.CrossingQuotient.mem_span_t _) ⟨(k : ℕ) + 1, by omega⟩ :=
          MvPolynomial.CrossingQuotient.Resolution.lineUGen_eq_lineGen_succ _ _ _ _ _ _

  haveI : Etale (C.g n) := MorphismProperty.pullback_snd _ _ (C.f_etale n)
  have L3gen' : ∀ (I : (C.Res n).IdealSheafData) (Z : TopologicalSpace.Closeds (C.Res n)),
      I = Scheme.IdealSheafData.vanishingIdeal Z → IsReduced (pullback (C.g n) I.subschemeι) := by
    rintro I Z rfl
    haveI := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Z
    haveI : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
    exact E9CP.L3gen.isReduced_of_etale (pullback.snd (C.g n) (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)
  have L3exc : ∀ k : Fin (C.thick n - 1), IsReduced (pullback (C.g n) (Fc (C.thick n) ⟨(k : ℕ) + 1, by omega⟩).subschemeι) :=
    fun k => L3gen' _ _ (L1exc k)
  let lam : Fin 2 → C.Res n := Fin.cases
    (MvPolynomial.CrossingQuotient.Resolution.lineGen ((q : ℕ) : O) (C.thick n) (Ideal.span {((q : ℕ) : O)})
      (MvPolynomial.CrossingQuotient.mem_span_t _) ⟨0, C.one_le_thick n⟩)
    (fun _ => MvPolynomial.CrossingQuotient.Resolution.lineUGen ((q : ℕ) : O) (C.thick n) (Ideal.span {((q : ℕ) : O)})
      (MvPolynomial.CrossingQuotient.mem_span_t _) ⟨C.thick n - 1, by have := C.one_le_thick n; omega⟩)
  have L1end : ∀ j : Fin 2, ((Fc (C.thick n) (Fin.cases 0 (fun _ => Fin.last _) j)).support : Set (MvPolynomial.CrossingQuotient.Resolution ((q : ℕ) : O) (C.thick n))) = closure {lam j} := by
    intro j
    refine Fin.cases ?_ (fun j1 => ?_) j
    · have h := E9CP.Model.eq_vanishingIdeal_closure_lineGen ((q : ℕ) : O) (C.thick n)
        (Fc (C.thick n)) hFe ⟨0, C.one_le_thick n⟩
      simp only [Fin.cases_zero, lam]
      rw [show (0 : Fin (C.thick n + 1)) = ⟨((⟨0, C.one_le_thick n⟩ : Fin (C.thick n)) : ℕ), by omega⟩ from rfl, h,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    · have h := E9CP.Model.eq_vanishingIdeal_closure_lineUGen_last ((q : ℕ) : O) (C.thick n)
        (Fc (C.thick n)) hFe ⟨C.thick n - 1, by have := C.one_le_thick n; omega⟩ (by have := C.one_le_thick n; simp only; omega)
      simp only [Fin.cases_succ, lam]
      rw [h, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
  have L3end : ∀ j : Fin 2, IsReduced (pullback (C.g n) (Fc (C.thick n) (Fin.cases 0 (fun _ => Fin.last _) j)).subschemeι) := by
    intro j
    refine Fin.cases ?_ (fun j1 => ?_) j
    · have h := E9CP.Model.eq_vanishingIdeal_closure_lineGen ((q : ℕ) : O) (C.thick n)
        (Fc (C.thick n)) hFe ⟨0, C.one_le_thick n⟩
      simp only [Fin.cases_zero]
      exact L3gen' _ _ (by rw [show (0 : Fin (C.thick n + 1)) = ⟨((⟨0, C.one_le_thick n⟩ : Fin (C.thick n)) : ℕ), by omega⟩ from rfl]; exact h)
    · have h := E9CP.Model.eq_vanishingIdeal_closure_lineUGen_last ((q : ℕ) : O) (C.thick n)
        (Fc (C.thick n)) hFe ⟨C.thick n - 1, by have := C.one_le_thick n; omega⟩ (by have := C.one_le_thick n; simp only; omega)
      simp only [Fin.cases_succ]
      exact L3gen' _ _ h
  have L4 : ∀ j : Fin 2, (C.g n).base ⁻¹' {lam j} = {C.ξY (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ n j (hU j)} := by
    have h4 := E9CP.Asm.preimage_g_lineGen_zero_and_lineUGen_last 𝔛 O ρO hϖ κ toκ H hξ n hU
    intro j
    refine Fin.cases ?_ (fun j1 => ?_) j
    · simp only [Fin.cases_zero, lam]
      rw [E9CP.Model.lineGen_congr_ideal _ _ _ (V3AsmLevel.p_mem_maximalIdeal O hϖ) hϖ.symm]
      exact h4.1
    · have hj1 : j1.succ = 1 := Fin.ext (by have := j1.2; simp only [Fin.val_succ, Fin.val_one]; omega)
      simp only [Fin.cases_succ, lam, hj1]
      rw [E9CP.Model.lineUGen_congr_ideal _ _ _ (V3AsmLevel.p_mem_maximalIdeal O hϖ) hϖ.symm]
      exact h4.2
  have key := V3Glue.ChartInput.comap_iotaY_compG_chainPosPrime_eq C (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H)
    (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ n (Fc (C.thick n))
    L1exc L3exc hU lam L1end L3end L4 d
  rw [V3AsmLevel.comp_def, ← V3AsmLevel.chainPos'_eq]
  exact key

private theorem label
    (Fc : ∀ e : ℕ, Fin (e + 1) → (MvPolynomial.CrossingQuotient.Resolution ((q : ℕ) : O) e).IdealSheafData)
    (hF : ∀ (e : ℕ) (i : Fin e) (k : Fin (e + 1)), (Fc e k).comap (MvPolynomial.CrossingQuotient.Resolution.ι ((q : ℕ) : O) e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient O ((q : ℕ) : O)))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {MvPolynomial.CrossingQuotient.V ((q : ℕ) : O)}
          else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {MvPolynomial.CrossingQuotient.U ((q : ℕ) : O)} else ⊤))) :
    ∀ (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (d : Fin ((V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n + 1)),
      (V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n d)).comap ((V3AsmLevel.toDR 𝔛 O ρO κ toκ hϖ H) ⁻¹ᵁ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n).ι =
        (Fc ((V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n) d).comap ((V3AsmLevel.chartIso 𝔛 O ρO κ toκ hϖ H n).inv ≫ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).g n) := by
  intro n d
  have key := comap_ιY_comp_eq 𝔛 O ρO hϖ κ toκ H hξ Fc hF n d

  have hι : (V3AsmLevel.D 𝔛 O ρO κ toκ hϖ H).ιY n = (V3AsmLevel.chartIso 𝔛 O ρO κ toκ hϖ H n).hom ≫ ((V3AsmLevel.toDR 𝔛 O ρO κ toκ hϖ H) ⁻¹ᵁ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n).ι :=
    (IsPullback.isoIsPullback_hom_snd _ _ _ _).symm
  rw [hι] at key

  have key2 : ((V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n d)).comap
      ((V3AsmLevel.chartIso 𝔛 O ρO κ toκ hϖ H n).hom ≫ ((V3AsmLevel.toDR 𝔛 O ρO κ toκ hϖ H) ⁻¹ᵁ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n).ι)).comap
        (V3AsmLevel.chartIso 𝔛 O ρO κ toκ hϖ H n).inv =
      ((Fc ((V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n) d).comap ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).g n)).comap (V3AsmLevel.chartIso 𝔛 O ρO κ toκ hϖ H n).inv :=
    congrArg (fun I => Scheme.IdealSheafData.comap I (V3AsmLevel.chartIso 𝔛 O ρO κ toκ hϖ H n).inv) key
  rw [Scheme.IdealSheafData.comap_comp]
  first
  | rw [← key2]
  | erw [← key2]
  first
  | rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id_assoc]
  | erw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id_assoc]

end E9CP.Asm
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

namespace E9CP
namespace Asm

open ModularCurve MvPolynomial MvPolynomial.CrossingQuotient

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ) (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0)

private theorem comap_ιY_comp_inr_of_ne (n m : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (hmn : m ≠ n) (k : Fin ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick m - 1)) :
    (V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inr ⟨m, k⟩)).comap ((V3AsmLevel.D 𝔛 O ρO κ toκ hϖ H).ιY n) = ⊤ := by
  let C := V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_preimage, TopologicalSpace.Closeds.coe_bot, Set.preimage_eq_empty_iff, Set.disjoint_left]
  rintro y hy ⟨z, rfl⟩

  have h1 : C.toGlueInput.toDR (C.toGlueInput.ιY n z) = C.x m := by
    rw [V3AsmLevel.comp_def] at hy
    exact V3Glue.ChartInput.exc_image' C (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H)
      (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ H.hxcl m k _ hy
  have h2 : C.toGlueInput.toDR (C.toGlueInput.ιY n z) = ((C.q n).base z).1 := by
    have h := congr($(C.toGlueInput.ιY_toDR n).base z)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    exact h.trans (by simp; rfl)
  have h3 : C.x m ∈ (C.U n : Set (ModularCurve.DRLevel.XO (N₀ := N₀) ρO)) := by rw [← h1, h2]; exact ((C.q n).base z).2
  exact C.x_not_mem_U n m hmn h3

private theorem prod_comp_comap_ιY [Fintype (V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO))] (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) :
    (∏ v, V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ v).comap ((V3AsmLevel.D 𝔛 O ρO κ toκ hϖ H).ιY n) =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ((q : ℕ) : O)})).comap
        ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).toB n) := by
  classical
  let C := V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H
  haveI hmaxI : (Ideal.span {((q : ℕ) : O)} : Ideal O).IsMaximal := hϖ ▸ IsLocalRing.maximalIdeal.isMaximal O
  haveI hredI : IsReduced (O ⧸ (Ideal.span {((q : ℕ) : O)} : Ideal O)) := by
    letI := Ideal.Quotient.field (Ideal.span {((q : ℕ) : O)} : Ideal O); infer_instance
  have hex := fun e => MvPolynomial.CrossingQuotient.Resolution.exists_idealSheafData_chartTable ((q : ℕ) : O) e
  choose Fc hF using hex
  have he : 1 ≤ C.thick n := C.one_le_thick n

  let F : C.Comps → (C.Res n).IdealSheafData := fun v => Sum.elim
    (fun j : Fin 2 => Fin.cases (Fc (C.thick n) 0) (fun _ => Fc (C.thick n) (Fin.last (C.thick n))) j)
    (fun mk : (Σ m : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO), Fin (C.thick m - 1)) =>
      if h : mk.1 = n then Fc (C.thick n) ⟨(mk.2 : ℕ) + 1, by have h1 := mk.2.2; have h2 : C.thick mk.1 = C.thick n := (by rw [h]); omega⟩ else ⊤) v
  have hF0 : F (Sum.inl 0) = Fc (C.thick n) 0 := rfl
  have hF1 : F (Sum.inl 1) = Fc (C.thick n) (Fin.last (C.thick n)) := rfl
  have hFn : ∀ k : Fin (C.thick n - 1), F (Sum.inr ⟨n, k⟩) = Fc (C.thick n) ⟨(k : ℕ) + 1, by omega⟩ := fun k => by
    simp only [F, Sum.elim_inr, dite_true]
  have hFm : ∀ (m : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (hm : m ≠ n) (k : Fin (C.thick m - 1)), F (Sum.inr ⟨m, k⟩) = ⊤ := fun m hm k => by
    simp only [F, Sum.elim_inr, dif_neg hm]

  have hcomp : ∀ v, (C.compG (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H)
      (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ v).comap (C.toGlueInput.ιY n) = (F v).comap (C.g n) := by
    have key := fun d : Fin (C.thick n + 1) => comap_ιY_comp_eq 𝔛 O ρO hϖ κ toκ H hξ Fc hF n d
    rintro (j | ⟨m, k⟩)
    · refine Fin.cases ?_ (fun j1 => ?_) j
      · have h := key 0
        rw [← V3AsmLevel.chainPos'_eq, show ((0 : Fin (C.thick n + 1)) : ℕ) = 0 from rfl, V3Glue.ChartInput.chainPos'_zero,
          V3AsmLevel.comp_def] at h
        rw [hF0]; exact h
      · have h := key (Fin.last (C.thick n))
        rw [← V3AsmLevel.chainPos'_eq, Fin.val_last, V3Glue.ChartInput.chainPos'_of_le C n (C.thick n) le_rfl, V3AsmLevel.comp_def] at h
        have hj1 : j1.succ = 1 := Fin.ext (by have := j1.2; simp only [Fin.val_succ, Fin.val_one]; omega)
        rw [hj1, hF1]; exact h
    · by_cases hm : m = n
      · subst hm
        have h := key ⟨(k : ℕ) + 1, by omega⟩
        rw [← V3AsmLevel.chainPos'_eq, show ((⟨(k : ℕ) + 1, by omega⟩ : Fin (C.thick m + 1)) : ℕ) = (k : ℕ) + 1 from rfl,
          V3Glue.ChartInput.chainPos'_succ, V3AsmLevel.comp_def] at h
        rw [hFn]; exact h
      · rw [hFm m hm k, Scheme.IdealSheafData.comap_top, ← V3AsmLevel.comp_def]
        exact comap_ιY_comp_inr_of_ne 𝔛 O ρO hϖ κ toκ H hξ n m hm k

  have hprodF : ∏ v, F v = ∏ d : Fin (C.thick n + 1), Fc (C.thick n) d := by
    rw [Fintype.prod_sum_type, Fin.prod_univ_two, hF0, hF1, Fintype.prod_sigma,
      Finset.prod_eq_single n (fun m _ hm => by simp only [hFm m hm, ← Scheme.IdealSheafData.one_eq_top, Finset.prod_const_one]) (fun h => absurd (Finset.mem_univ n) h)]
    simp only [hFn]

    have aux : ∀ (t : ℕ) (ht : 1 ≤ t) (G : Fin (t + 1) → (C.Res n).IdealSheafData),
        ∏ d, G d = G 0 * G (Fin.last t) * ∏ k : Fin (t - 1), G ⟨(k : ℕ) + 1, by omega⟩ := by
      intro t ht G
      obtain ⟨e, rfl⟩ : ∃ e, t = e + 1 := ⟨t - 1, by omega⟩
      rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc, mul_assoc, mul_comm (∏ _ : Fin e, _)]
      congr 2
    exact (aux (C.thick n) he (Fc (C.thick n))).symm

  have hprod : ∏ v, F v = (Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ((q : ℕ) : O)})).comap
      (C.ρ n ≫ C.σ n) := by
    rw [hprodF, (MvPolynomial.CrossingQuotient.Resolution.prod_pow_eq_ofIdealTop_uSec_and_vSec_and_tSec ((q : ℕ) : O) (C.thick n)
      (Fc (C.thick n)) (hF (C.thick n))).2.2, Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]
    rfl
  have key := V3Glue.ChartInput.prod_compG_comap_iotaY_eq C (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H)
    (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ n _ F hcomp hprod
  simp only [V3AsmLevel.comp_def]
  exact key

private theorem prod_comp_comap_ιY' [Fintype (V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO))] (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) :
    (∏ v, V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ v).comap ((V3AsmLevel.D 𝔛 O ρO κ toκ hϖ H).ιY n) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).toB n).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ((q : ℕ) : O))}) := by
  rw [prod_comp_comap_ιY, Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]
  rfl

end E9CP.Asm
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

noncomputable section
namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.basicOpen_res LocallyOfFiniteType.stalkMap Surjective Scheme.IdealSheafData.support_comap Scheme.fromSpecStalk_closedPoint Scheme.IdealSheafData.one_eq_top Scheme.IdealSheafData.comap_comp morphismRestrict_base_coe Scheme.IdealSheafData.coe_support_vanishingIdeal LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom Scheme.range_fromSpecStalk FormallyUnramified.stalkMap IsAffine Scheme.Hom.image_top_eq_opensRange LocallyOfFiniteType Spec Spec.map Scheme Smooth Scheme.IdealSheafData.vanishingIdeal isReduced_of_isReduced_stalk Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.Hom.comp_base Etale.etale_appLE Scheme.IdealSheafData.ext_of_iSup_eq_top IsReduced Scheme.mem_zeroLocus_iff IsLocallyNoetherian.component_noetherian isAffineOpen_top Scheme.preimage_basicOpen_top Etale IsReduced.component_reduced Scheme.SpecMap_stalkMap_fromSpecStalk Scheme.basicOpen_mul IsAffineOpen Scheme.IdealSheafData.support_eq_bot_iff FormallyUnramified Scheme.IdealSheafData.comap Scheme.homOfLE_ι Scheme.IdealSheafData.ofIdealTop Scheme.IdealSheafData.ext Etale.iff_flat_and_formallyUnramified Scheme.Hom.comp_apply basicOpen_eq_of_affine Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion v3_isReduced_pullback_subschemeι_of_isOpenImmersion Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Scheme.IdealSheafData.comap_ofIdealTop"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen basicOpen_res fromSpecStalk IdealSheafData.support_comap fromSpecStalk_closedPoint IdealSheafData.one_eq_top IdealSheafData.comap_comp IdealSheafData.coe_support_vanishingIdeal Hom mk Γ empty range_fromSpecStalk Hom.image_top_eq_opensRange IdealSheafData.vanishingIdeal IdealSheafData.comap_top Hom.comp_base zeroLocus IdealSheafData.ext_of_iSup_eq_top mem_zeroLocus_iff affineOpens basicOpen preimage_basicOpen_top SpecMap_stalkMap_fromSpecStalk basicOpen_mul isBasis_affineOpens IdealSheafData.support_eq_bot_iff IdealSheafData.comap Opens residue homOfLE_ι le_iff_specializes IdealSheafData.ofIdealTop IdealSheafData.ext restrict Hom.comp_apply IdealSheafData ΓSpecIso IdealSheafData.ideal_comap_of_isOpenImmersion IdealSheafData.isReduced_subscheme_vanishingIdeal IdealSheafData.comap_ofIdealTop"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "radical support_comap radical_ideal one_eq_top comap_comp coe_support_vanishingIdeal mk map subscheme vanishingIdeal comap_top ideal ext_of_iSup_eq_top support_eq_bot_iff subschemeι comap ofIdealTop support mem_support_iff_of_mem ofIdealTop_ideal ideal_comap_of_isOpenImmersion v3_comap_eq_vanishingIdeal_of_isReduced isReduced_subscheme_vanishingIdeal comap_ofIdealTop comap_mul prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup eq_of_forall_comap_openCover_eq"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

open TopologicalSpace

attribute [local instance] AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal

private theorem comap_vanishingIdeal_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (Z : Closeds Y) :
    (vanishingIdeal Z).comap f = vanishingIdeal ⟨f.base ⁻¹' (Z : Set Y), Z.isClosed.preimage f.continuous⟩ := by
  haveI := v3_isReduced_pullback_subschemeι_of_isOpenImmersion f (vanishingIdeal Z)
  exact (v3_comap_eq_vanishingIdeal_of_isReduced (vanishingIdeal Z) f).trans rfl

private theorem comap_finset_prod {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (s : Finset ι) (I : ι → Y.IdealSheafData) :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [comap_top]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, comap_mul, ih]

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

namespace V3Glue
p2m_export "V3Glue" "LevelSite.Node LevelSite.xpt LevelSite.chartData ChartInput.exc_image' ChartInput.chainPos'_zero ChartInput.chainPos'_succ ChartInput.chainPos'_of_le ChartInput Aux.mem_of_closure_singleton_inter_nonempty ChartInput.comap_iotaY_compG_chainPosPrime_eq ChartInput.prod_compG_comap_iotaY_eq"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl compG exc_image' ξY chainPos'_zero chainPos'_succ chainPos'_of_le xU vertex vertex_def Y q a j j_q toGlueInput hq g q_f toB toB_eq πX Res X0 f_etale U σ mk S x_not_mem_U one_le_thick B ρ Vc x thick f_mem_Vc_iff x_mem_U f mem_X0 comap_iotaY_compG_chainPosPrime_eq prod_compG_comap_iotaY_eq"
p2m_open "V3Glue.ChartInput V3Glue"

open V3Glue.Aux

p2m_open "AlgebraicGeometry P2MW.S_V3AsmLevel_comp_prod.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3AsmLevel_comp_prod.AlgebraicGeometry.Scheme.IdealSheafData"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
  (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

private theorem _root_.V3Glue.ChartInput.comap_ιX0_compG_inr (hx : ∀ n, IsClosed ({C.x n} : Set X)) (n : N) (k : Fin (C.thick n - 1)) :
    (C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).comap C.toGlueInput.ιX0 = ⊤ := by
  rw [← support_eq_bot_iff, support_comap]
  ext y0
  simp only [Closeds.coe_preimage, Set.mem_preimage, Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hy
  have h1 := C.exc_image' hRF gRes hgRes ξ hξ hx n k _ hy
  have h2 : C.toGlueInput.toDR (C.toGlueInput.ιX0 y0) = y0.1 := by
    rw [← Scheme.Hom.comp_apply, C.toGlueInput.ιX0_toDR]; rfl
  rw [h2] at h1
  exact ((C.mem_X0 _).mp y0.2) n h1

p2m_export "V3Glue.ChartInput" "comap_ιX0_compG_inr"

private theorem _root_.V3Glue.ChartInput.comap_ιX0_compG_inl (j : Fin 2) :
    (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).comap C.toGlueInput.ιX0 =
      vanishingIdeal ⟨closure ({(⟨ξ j, hξ j⟩ : C.X0)} : Set C.X0), isClosed_closure⟩ := by
  rw [compG, comap_vanishingIdeal_of_isOpenImmersion]
  congr 1
  ext1
  change C.toGlueInput.ιX0.base ⁻¹' closure {C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)} = closure {(⟨ξ j, hξ j⟩ : C.X0)}
  rw [ηG_inl, C.toGlueInput.ιX0.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    C.toGlueInput.ιX0.continuous]
  congr 1
  ext z
  constructor
  · intro hz; exact C.toGlueInput.ιX0.isOpenEmbedding.injective hz
  · rintro rfl; rfl

p2m_export "V3Glue.ChartInput" "comap_ιX0_compG_inl"

private theorem _root_.V3Glue.ChartInput.compG_prod_comap_ιX0_eq [Fintype N] (hx : ∀ n, IsClosed ({C.x n} : Set X))
    (J : (C.X0 : Scheme.{0}).IdealSheafData) (hrad : J.radical = J)
    (hdisj : Disjoint (⟨closure ({(⟨ξ 0, hξ 0⟩ : C.X0)} : Set C.X0), isClosed_closure⟩ : Closeds C.X0)
      ⟨closure ({(⟨ξ 1, hξ 1⟩ : C.X0)} : Set C.X0), isClosed_closure⟩)
    (hsupp : J.support = (⟨closure ({(⟨ξ 0, hξ 0⟩ : C.X0)} : Set C.X0), isClosed_closure⟩ : Closeds C.X0) ⊔
      ⟨closure ({(⟨ξ 1, hξ 1⟩ : C.X0)} : Set C.X0), isClosed_closure⟩) :
    (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 = J := by
  classical
  rw [comap_finset_prod, Fintype.prod_sum_type]
  have hinr : ∏ b : (Σ n : N, Fin (C.thick n - 1)), (C.compG hRF gRes hgRes ξ hξ (Sum.inr b)).comap C.toGlueInput.ιX0 = 1 :=
    Finset.prod_eq_one fun b _ => by
      obtain ⟨n, k⟩ := b
      rw [C.comap_ιX0_compG_inr hRF gRes hgRes ξ hξ hx n k]; rfl
  rw [hinr, mul_one]
  simp_rw [C.comap_ιX0_compG_inl hRF gRes hgRes ξ hξ]
  let Z : Fin 2 → Closeds C.X0 := fun j => ⟨closure ({(⟨ξ j, hξ j⟩ : C.X0)} : Set C.X0), isClosed_closure⟩
  change ∏ j, vanishingIdeal (Z j) = J
  apply prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup Z
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hdisj
    · exact hdisj.symm
    · exact absurd rfl hij
  · exact hrad
  · rw [hsupp]
    apply le_antisymm
    · exact sup_le (le_iSup Z 0) (le_iSup Z 1)
    · refine iSup_le fun j => ?_
      fin_cases j
      · exact le_sup_left
      · exact le_sup_right

p2m_export "V3Glue.ChartInput" "compG_prod_comap_ιX0_eq"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

namespace V3Glue
p2m_export "V3Glue" "LevelSite.Node LevelSite.xpt LevelSite.chartData ChartInput.exc_image' ChartInput.chainPos'_zero ChartInput.chainPos'_succ ChartInput.chainPos'_of_le ChartInput Aux.mem_of_closure_singleton_inter_nonempty ChartInput.comap_iotaY_compG_chainPosPrime_eq ChartInput.prod_compG_comap_iotaY_eq"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl compG exc_image' ξY chainPos'_zero chainPos'_succ chainPos'_of_le xU vertex vertex_def Y q a j j_q toGlueInput hq g q_f toB toB_eq πX Res X0 f_etale U σ mk S x_not_mem_U one_le_thick B ρ Vc x thick f_mem_Vc_iff x_mem_U f mem_X0 comap_iotaY_compG_chainPosPrime_eq prod_compG_comap_iotaY_eq"
p2m_open "V3Glue.ChartInput V3Glue"

open V3Glue.Aux

p2m_open "AlgebraicGeometry P2MW.S_V3AsmLevel_comp_prod.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3AsmLevel_comp_prod.AlgebraicGeometry.Scheme.IdealSheafData"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
  (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

section glue

variable [Fintype N] {T : Scheme.{0}} (b : C.toGlueInput.glued ⟶ T)

private theorem _root_.V3Glue.ChartInput.compG_prod_eq_comap (K : T.IdealSheafData)
    (hX0 : (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 = K.comap (C.toGlueInput.ιX0 ≫ b))
    (hY : ∀ n, (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) = K.comap (C.toGlueInput.ιY n ≫ b)) :
    ∏ v, C.compG hRF gRes hgRes ξ hξ v = K.comap b := by
  apply eq_of_forall_comap_openCover_eq C.toGlueInput.openCover
  rintro (_ | n)
  · exact hX0.trans (comap_comp K C.toGlueInput.ιX0 b)
  · exact (hY n).trans (comap_comp K (C.toGlueInput.ιY n) b)

p2m_export "V3Glue.ChartInput" "compG_prod_eq_comap"

private theorem _root_.V3Glue.ChartInput.compG_prod_eq_ofIdealTop_span (r : Γ(T, ⊤))
    (hX0 : (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 =
      (ofIdealTop (Ideal.span {r})).comap (C.toGlueInput.ιX0 ≫ b))
    (hY : ∀ n, (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) =
      (ofIdealTop (Ideal.span {r})).comap (C.toGlueInput.ιY n ≫ b)) :
    ∏ v, C.compG hRF gRes hgRes ξ hξ v = ofIdealTop (Ideal.span {b.appTop.hom r}) := by
  rw [C.compG_prod_eq_comap hRF gRes hgRes ξ hξ b _ hX0 hY, comap_ofIdealTop, Ideal.map_span, Set.image_singleton]

p2m_export "V3Glue.ChartInput" "compG_prod_eq_ofIdealTop_span"

private theorem compG_prod_ideal_eq_span_natCast' (p : ℕ)
    (hX0 : (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 =
      (ofIdealTop (Ideal.span {((p : ℕ) : Γ(T, ⊤))})).comap (C.toGlueInput.ιX0 ≫ b))
    (hY : ∀ n, (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) =
      (ofIdealTop (Ideal.span {((p : ℕ) : Γ(T, ⊤))})).comap (C.toGlueInput.ιY n ≫ b))
    (U : C.toGlueInput.glued.affineOpens) :
    (∏ v, C.compG hRF gRes hgRes ξ hξ v).ideal U = Ideal.span {((p : ℕ) : Γ(C.toGlueInput.glued, U))} := by
  rw [C.compG_prod_eq_ofIdealTop_span hRF gRes hgRes ξ hξ b _ hX0 hY, ofIdealTop_ideal, Ideal.map_span,
    Set.image_singleton, map_natCast, map_natCast]

end glue
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

namespace V3Glue
p2m_export "V3Glue" "LevelSite.Node LevelSite.xpt LevelSite.chartData ChartInput.exc_image' ChartInput.chainPos'_zero ChartInput.chainPos'_succ ChartInput.chainPos'_of_le ChartInput Aux.mem_of_closure_singleton_inter_nonempty ChartInput.comap_iotaY_compG_chainPosPrime_eq ChartInput.prod_compG_comap_iotaY_eq"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl compG exc_image' ξY chainPos'_zero chainPos'_succ chainPos'_of_le xU vertex vertex_def Y q a j j_q toGlueInput hq g q_f toB toB_eq πX Res X0 f_etale U σ mk S x_not_mem_U one_le_thick B ρ Vc x thick f_mem_Vc_iff x_mem_U f mem_X0 comap_iotaY_compG_chainPosPrime_eq prod_compG_comap_iotaY_eq"
p2m_open "V3Glue.ChartInput V3Glue"

open V3Glue.Aux

p2m_open "AlgebraicGeometry P2MW.S_V3AsmLevel_comp_prod.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3AsmLevel_comp_prod.AlgebraicGeometry.Scheme.IdealSheafData"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

private def _root_.V3Glue.ChartInput.toBase : C.toGlueInput.glued ⟶ C.B := C.toGlueInput.toDR ≫ C.πX

p2m_export "V3Glue.ChartInput" "toBase"
@[reassoc]
private theorem ιX0_toBase : C.toGlueInput.ιX0 ≫ C.toBase = (C.X0 : X.Opens).ι ≫ C.πX := by
  rw [toBase, ← Category.assoc, C.toGlueInput.ιX0_toDR]; rfl

@[reassoc]
private theorem ιY_toBase (n : N) : C.toGlueInput.ιY n ≫ C.toBase = C.toB n := by
  rw [toBase, ← Category.assoc, C.toGlueInput.ιY_toDR, toB_eq, Category.assoc]; rfl

section glueBase

variable [Fintype N]
  (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

private theorem _root_.V3Glue.ChartInput.compG_prod_eq_comap_toBase (P : C.B.IdealSheafData)
    (hX0 : (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 = P.comap ((C.X0 : X.Opens).ι ≫ C.πX))
    (hY : ∀ n, (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) = P.comap (C.toB n)) :
    ∏ v, C.compG hRF gRes hgRes ξ hξ v = P.comap C.toBase :=
  C.compG_prod_eq_comap hRF gRes hgRes ξ hξ C.toBase P (by rw [hX0, ιX0_toBase]; rfl)
    (fun n => by rw [hY, ιY_toBase]; rfl)

p2m_export "V3Glue.ChartInput" "compG_prod_eq_comap_toBase"

private theorem _root_.V3Glue.ChartInput.compG_prod_ideal_eq_span_natCast (p : ℕ)
    (hX0 : (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 =
      (ofIdealTop (Ideal.span {((p : ℕ) : Γ(C.B, ⊤))})).comap ((C.X0 : X.Opens).ι ≫ C.πX))
    (hY : ∀ n, (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) =
      (ofIdealTop (Ideal.span {((p : ℕ) : Γ(C.B, ⊤))})).comap (C.toB n))
    (U : C.toGlueInput.glued.affineOpens) :
    (∏ v, C.compG hRF gRes hgRes ξ hξ v).ideal U = Ideal.span {((p : ℕ) : Γ(C.toGlueInput.glued, U))} := by
  rw [C.compG_prod_eq_comap_toBase hRF gRes hgRes ξ hξ _ hX0 hY, comap_ofIdealTop, Ideal.map_span, Set.image_singleton,
    ofIdealTop_ideal, Ideal.map_span, Set.image_singleton, map_natCast, map_natCast]

p2m_export "V3Glue.ChartInput" "compG_prod_ideal_eq_span_natCast"
end glueBase
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

end
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

noncomputable section

namespace E9CP
namespace X0

p2m_open "AlgebraicGeometry P2MW.S_V3AsmLevel_comp_prod.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3AsmLevel_comp_prod.AlgebraicGeometry.Scheme.IdealSheafData ModularCurve"

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ) (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ)

local notation "ℭ" => V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H

private def Jsf : ((ℭ).X0 : Scheme.{0}).IdealSheafData :=
  (ofIdealTop (Ideal.span {((q : ℕ) : Γ((ℭ).B, ⊤))})).comap (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens).ι ≫ (ℭ).πX)

private theorem Jsf_eq : Jsf 𝔛 O ρO hϖ κ toκ H = ofIdealTop (Ideal.span {((q : ℕ) : Γ(((ℭ).X0 : Scheme.{0}), ⊤))}) := by
  rw [Jsf, comap_ofIdealTop, Ideal.map_span, Set.image_singleton, map_natCast]

private theorem Jsf_ideal (U : (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens) : Scheme.{0}).affineOpens) :
    (Jsf 𝔛 O ρO hϖ κ toκ H).ideal U = Ideal.span {((q : ℕ) : Γ(((ℭ).X0 : Scheme.{0}), U))} := by
  rw [Jsf_eq, ofIdealTop_ideal, Ideal.map_span, Set.image_singleton, map_natCast]

private theorem Jsf_radical : (Jsf 𝔛 O ρO hϖ κ toκ H).radical = Jsf 𝔛 O ρO hϖ κ toκ H := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [radical_ideal, Jsf_ideal]

  have hmax : (Ideal.span {((q : ℕ) : O)}).IsMaximal := hϖ ▸ IsLocalRing.maximalIdeal.isMaximal O
  have hU' : IsAffineOpen ((((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens).ι) ''ᵁ (U : (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens) : Scheme.{0}).Opens)) :=
    U.2.image_of_isOpenImmersion _
  have hR := ModularCurve.DRModelPackageLevel.isRadical_span_natCast_sections_XO N₀ q hqN 𝔛 O ρO hmax ⟨_, hU'⟩
  let e := (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens).ι).appIso (U : (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens) : Scheme.{0}).Opens)

  have hcomap : Ideal.comap e.inv.hom (Ideal.span {((q : ℕ) : Γ(ModularCurve.DRLevel.XO (N₀ := N₀) ρO, (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens).ι) ''ᵁ U))}) =
      Ideal.span {((q : ℕ) : Γ(((ℭ).X0 : Scheme.{0}), U))} := by
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
      obtain ⟨c, hc⟩ := hx
      rw [Ideal.mem_span_singleton]
      refine ⟨e.hom.hom c, ?_⟩
      have := congrArg e.hom.hom hc
      rw [← CommRingCat.comp_apply, e.inv_hom_id] at this
      simpa [map_mul, map_natCast] using this
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span rfl
  rw [← hcomap, ← Ideal.comap_radical, hR.radical]

private theorem basicOpen_natCast_eq :
    (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens) : Scheme.{0}).basicOpen ((q : ℕ) : Γ(((ℭ).X0 : Scheme.{0}), ⊤)) =
      (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens).ι ≫ V3AsmLevel.πX (N₀ := N₀) O ρO) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
  have h : ((q : ℕ) : Γ(((ℭ).X0 : Scheme.{0}), ⊤)) =
      ((((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens).ι ≫ V3AsmLevel.πX (N₀ := N₀) O ρO).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ((q : ℕ) : O)) := by
    rw [map_natCast, map_natCast]
  rw [h, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]

private theorem mem_support_Jsf_iff (x : ↥(ℭ).X0) :
    x ∈ (Jsf 𝔛 O ρO hϖ κ toκ H).support ↔
      (x : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∉ (V3AsmLevel.πX (N₀ := N₀) O ρO) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens) : Scheme.{0}).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  refine (mem_support_iff_of_mem (I := Jsf 𝔛 O ρO hϖ κ toκ H) (U := ⟨U, hU⟩) hxU).trans ?_
  rw [Jsf_ideal, Scheme.mem_zeroLocus_iff]

  have hres : ((q : ℕ) : Γ(((ℭ).X0 : Scheme.{0}), U)) =
      ((((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens) : Scheme.{0}).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        ((q : ℕ) : Γ(((ℭ).X0 : Scheme.{0}), ⊤)) := by rw [map_natCast]
  have hbU : (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens) : Scheme.{0}).basicOpen ((q : ℕ) : Γ(((ℭ).X0 : Scheme.{0}), U)) =
      U ⊓ (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens).ι ≫ V3AsmLevel.πX (N₀ := N₀) O ρO) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
    rw [hres, Scheme.basicOpen_res, basicOpen_natCast_eq]
  have key : x ∈ (((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens) : Scheme.{0}).basicOpen ((q : ℕ) : Γ(((ℭ).X0 : Scheme.{0}), U)) ↔
      (x : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∈ (V3AsmLevel.πX (N₀ := N₀) O ρO) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
    rw [hbU]
    exact ⟨fun h => h.2, fun h => ⟨hxU, h⟩⟩
  constructor
  · intro h hx
    exact h _ (Ideal.subset_span rfl) (key.mpr hx)
  · intro hx f hf hxf
    rw [SetLike.mem_coe, Ideal.mem_span_singleton'] at hf
    obtain ⟨c, rfl⟩ := hf
    rw [Scheme.basicOpen_mul] at hxf
    exact hx (key.mp hxf.2)

private theorem support_Jsf_eq (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (ℭ).X0) :
    (Jsf 𝔛 O ρO hϖ κ toκ H).support =
      (⟨closure ({(⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hξ 0⟩ : ↥(ℭ).X0)} : Set ↥(ℭ).X0), isClosed_closure⟩ : Closeds ↥(ℭ).X0) ⊔
        ⟨closure ({(⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hξ 1⟩ : ↥(ℭ).X0)} : Set ↥(ℭ).X0), isClosed_closure⟩ := by
  ext x
  change x ∈ (Jsf 𝔛 O ρO hϖ κ toκ H).support ↔
    x ∈ closure ({(⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hξ 0⟩ : ↥(ℭ).X0)} : Set ↥(ℭ).X0) ∪
      closure ({(⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hξ 1⟩ : ↥(ℭ).X0)} : Set ↥(ℭ).X0)
  refine (mem_support_Jsf_iff 𝔛 O ρO hϖ κ toκ H x).trans ?_
  constructor
  · intro hx
    rcases ModularCurve.DRModelPackageLevel.bcMap_genericPoint_specializes_or N₀ q hqN 𝔛 O ρO hϖ κ toκ
        x.1 hx with h | h
    · left
      rw [← specializes_iff_mem_closure]
      exact Topology.IsInducing.subtypeVal.specializes_iff.mp h
    · right
      rw [← specializes_iff_mem_closure]
      exact Topology.IsInducing.subtypeVal.specializes_iff.mp h
  ·
    have hcl : IsClosed {y : ↥(ℭ).X0 | (y : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∉ (V3AsmLevel.πX (N₀ := N₀) O ρO) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)} := by
      have : IsOpen {y : ↥(ℭ).X0 | (y : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∈ (V3AsmLevel.πX (N₀ := N₀) O ρO) ⁻¹ᵁ
          (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)} :=
        ((V3AsmLevel.πX (N₀ := N₀) O ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)).isOpen.preimage
          continuous_subtype_val
      simpa [Set.compl_setOf] using this.isClosed_compl
    have hξV : ∀ j, (V3AsmLevel.ξ 𝔛 O ρO κ toκ j) ∉ (V3AsmLevel.πX (N₀ := N₀) O ρO) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
      refine Fin.cases ?_ (fun i => ?_)
      · rw [V3AsmLevel.ξ_zero]; exact ModularCurve.DRLevel.bcMap_apply_notMem_preimage_basicOpen N₀ q O ρO κ toκ _
      · obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [show (0 : Fin 1).succ = (1 : Fin 2) from rfl, V3AsmLevel.ξ_one]
        exact ModularCurve.DRLevel.bcMap_apply_notMem_preimage_basicOpen N₀ q O ρO κ toκ _
    rintro (h | h)
    · exact closure_minimal (Set.singleton_subset_iff.mpr (hξV 0)) hcl h
    · exact closure_minimal (Set.singleton_subset_iff.mpr (hξV 1)) hcl h

private theorem disjoint_closure_ξ (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (ℭ).X0) :
    Disjoint (⟨closure ({(⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hξ 0⟩ : ↥(ℭ).X0)} : Set ↥(ℭ).X0), isClosed_closure⟩ : Closeds ↥(ℭ).X0)
      ⟨closure ({(⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hξ 1⟩ : ↥(ℭ).X0)} : Set ↥(ℭ).X0), isClosed_closure⟩ := by
  rw [disjoint_iff, ← SetLike.coe_set_eq]
  change closure ({(⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hξ 0⟩ : ↥(ℭ).X0)} : Set ↥(ℭ).X0) ∩
      closure ({(⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hξ 1⟩ : ↥(ℭ).X0)} : Set ↥(ℭ).X0) = (∅ : Set ↥(ℭ).X0)
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨h0, h1⟩
  have h0' : (x : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∈ closure ({V3AsmLevel.ξ 𝔛 O ρO κ toκ 0} : Set (ModularCurve.DRLevel.XO (N₀ := N₀) ρO)) := by
    have := image_closure_subset_closure_image continuous_subtype_val (s := {(⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hξ 0⟩ : ↥(ℭ).X0)})
      ⟨x, h0, rfl⟩
    rwa [Set.image_singleton] at this
  have h1' : (x : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∈ closure ({V3AsmLevel.ξ 𝔛 O ρO κ toκ 1} : Set (ModularCurve.DRLevel.XO (N₀ := N₀) ρO)) := by
    have := image_closure_subset_closure_image continuous_subtype_val (s := {(⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hξ 1⟩ : ↥(ℭ).X0)})
      ⟨x, h1, rfl⟩
    rwa [Set.image_singleton] at this

  have hs0 : ({V3AsmLevel.ξ 𝔛 O ρO κ toκ 0} : Set (ModularCurve.DRLevel.XO (N₀ := N₀) ρO)) ⊆ Set.range ⇑(𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base := by
    rw [V3AsmLevel.ξ_zero, Set.singleton_subset_iff]; exact Set.mem_range_self _
  have hs1 : ({V3AsmLevel.ξ 𝔛 O ρO κ toκ 1} : Set (ModularCurve.DRLevel.XO (N₀ := N₀) ρO)) ⊆ Set.range ⇑(𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base := by
    rw [V3AsmLevel.ξ_one, Set.singleton_subset_iff]; exact Set.mem_range_self _
  have h0r := closure_mono hs0 h0'
  have h1r := closure_mono hs1 h1'
  obtain ⟨n, hn⟩ := ModularCurve.DRModelPackageLevel.exists_eq_crossingPt_of_mem_closure_of_mem_closure
    N₀ q hqN 𝔛 O ρO hϖ κ toκ _ h0r h1r
  exact ((V3AsmLevel.mem_X0_iff 𝔛 O ρO κ toκ hϖ H _).mp x.2) n hn

private theorem prod_comp_comap_ιX0 [Fintype (V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO))] (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (ℭ).X0) :
    (∏ v, V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ v).comap ((V3AsmLevel.D 𝔛 O ρO κ toκ hϖ H).ιX0) =
      (ofIdealTop (Ideal.span {((q : ℕ) : Γ((ℭ).B, ⊤))})).comap
        ((((ℭ).X0 : (ModularCurve.DRLevel.XO (N₀ := N₀) ρO).Opens)).ι ≫ (ℭ).πX) := by
  have hx : ∀ n, IsClosed ({(ℭ).x n} : Set (ModularCurve.DRLevel.XO (N₀ := N₀) ρO)) := fun n => H.hxcl n
  have key := (ℭ).compG_prod_comap_ιX0_eq (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H)
    (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ hx (Jsf 𝔛 O ρO hϖ κ toκ H)
    (Jsf_radical 𝔛 O ρO hϖ κ toκ H) (disjoint_closure_ξ 𝔛 O ρO hϖ κ toκ H hξ) (support_Jsf_eq 𝔛 O ρO hϖ κ toκ H hξ)
  simp only [V3AsmLevel.comp_def]
  exact key

private theorem comp_prod_of_hY [Fintype (V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO))] (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (ℭ).X0)
    (hY : ∀ n, (∏ v, V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ v).comap ((V3AsmLevel.D 𝔛 O ρO κ toκ hϖ H).ιY n) =
      (ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ((q : ℕ) : O)})).comap ((ℭ).toB n))
    (U : (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H).affineOpens) :
    (∏ v, V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ v).ideal U = Ideal.span {((q : ℕ) : Γ(V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H, U))} := by
  have hX0 := prod_comp_comap_ιX0 𝔛 O ρO hϖ κ toκ H hξ
  have hY' : ∀ n, (∏ v, (ℭ).compG (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H)
      (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ v).comap ((ℭ).toGlueInput.ιY n) =
      (ofIdealTop (Ideal.span {((q : ℕ) : Γ((ℭ).B, ⊤))})).comap ((ℭ).toB n) := by
    intro n
    have h := hY n
    simp only [V3AsmLevel.comp_def, map_natCast] at h
    exact h
  simp only [V3AsmLevel.comp_def] at hX0 ⊢
  exact (ℭ).compG_prod_ideal_eq_span_natCast (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H)
    (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ q hX0 hY' U

end E9CP.X0
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

end
p2m_reactivate "P2MW.S_V3AsmLevel_comp_prod.E9CP P2MW.S_V3AsmLevel_comp_prod.E9CP.L4"

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    [Fintype (V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO))] (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ)
    (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0) :
    ∀ U : (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H).affineOpens,
      (∏ v, V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ v).ideal U = Ideal.span {((q : ℕ) : Γ(V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H, U))} :=
  fun U => E9CP.X0.comp_prod_of_hY 𝔛 O ρO hϖ κ toκ H hξ (fun n => E9CP.Asm.prod_comp_comap_ιY 𝔛 O ρO hϖ κ toκ H hξ n) U

end S_V3AsmLevel_comp_prod
end P2MW
export P2MW.S_V3AsmLevel_comp_prod (solution)
