-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_moduleFinite_represents_isLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ef946d6e-7628-5d2c-847f-e82b4ab87412

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isLevel_iff_isDrinfeldBasisOver_comp_projMap
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_moduleFinite_represents_isDrinfeldBasisOver_of_two_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_moduleFinite_represents_isLevel
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_moduleFinite_represents_isLevel.WeierstrassCurve.DrinfeldGlobal"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_map map mk Δ VariableChange Projective DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom DrinfeldGlobal.isLevel_iff_isDrinfeldBasisOver_comp_projMap"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "GroupLaws RawDrinfeldPair.IsLevel LevelTransport Section RawDrinfeldPair cls IsVariableChangeHom IsCoefficientHom isPullback_projMap_of_isCoefficientHom isLevel_iff_isDrinfeldBasisOver_comp_projMap"
namespace RawRepReduce
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

open MvPolynomial

theorem gradedRingHom_ext {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T)
    (V : WeierstrassCurve.Projective T') (φ₁ φ₂ : projModelGradingCR W →+*ᵍ projModelGradingCR V)
    (hC : ∀ a : T, φ₁ (cls W (MvPolynomial.C a)) = φ₂ (cls W (MvPolynomial.C a)))
    (hX : ∀ i : Fin 3, φ₁ (cls W (X i)) = φ₂ (cls W (X i))) : φ₁ = φ₂ := by
  have key : φ₁.toRingHom.comp (Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal) =
      φ₂.toRingHom.comp (Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal) :=
    MvPolynomial.ringHom_ext (fun a ↦ hC a) (fun i ↦ hX i)
  refine GradedRingHom.ext fun x ↦ ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact RingHom.congr_fun key p

theorem projMap_eq_eqToHom_comp_projMap {T T' : Type u} [CommRing T] [CommRing T']
    (W : WeierstrassCurve.Projective T) (f : T →+* T') :
    ∀ {V₁ V₂ : WeierstrassCurve.Projective T'} (e : V₁ = V₂)
      (φ₁ : projModelGradingCR W →+*ᵍ projModelGradingCR V₁)
      (φ₂ : projModelGradingCR W →+*ᵍ projModelGradingCR V₂)
      (h₁ : HomogeneousIdeal.irrelevant (projModelGradingCR V₁) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ₁)
      (h₂ : HomogeneousIdeal.irrelevant (projModelGradingCR V₂) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ₂),
      (∀ a : T, φ₁ (cls W (MvPolynomial.C a)) = cls V₁ (MvPolynomial.C (f a))) →
      (∀ i : Fin 3, φ₁ (cls W (X i)) = cls V₁ (X i)) →
      (∀ a : T, φ₂ (cls W (MvPolynomial.C a)) = cls V₂ (MvPolynomial.C (f a))) →
      (∀ i : Fin 3, φ₂ (cls W (X i)) = cls V₂ (X i)) →
      Proj.map φ₁ h₁ = eqToHom (congrArg projModelCR e) ≫ Proj.map φ₂ h₂ := by
  rintro V₁ _ rfl φ₁ φ₂ h₁ h₂ hC₁ hX₁ hC₂ hX₂
  obtain rfl : φ₁ = φ₂ :=
    gradedRingHom_ext W V₁ φ₁ φ₂ (fun a ↦ (hC₁ a).trans (hC₂ a).symm) (fun i ↦ (hX₁ i).trans (hX₂ i).symm)
  simp

theorem eqToHom_comp_projModelStrCR {T : Type u} [CommRing T] :
    ∀ {V₁ V₂ : WeierstrassCurve.Projective T} (e : V₁ = V₂),
      eqToHom (congrArg projModelCR e) ≫ projModelStrCR V₂ = projModelStrCR V₁ := by
  rintro _ _ rfl; simp

theorem rawDrinfeldPair_ext {T : Type u} [CommRing T] :
    ∀ (x y : RawDrinfeldPair T) (e : x.curve = y.curve),
      x.P.1 ≫ eqToHom (congrArg projModelCR e) = y.P.1 →
      x.Q.1 ≫ eqToHom (congrArg projModelCR e) = y.Q.1 → x = y := by
  rintro ⟨xc, xP, xQ⟩ ⟨yc, yP, yQ⟩ e hP hQ
  cases e
  simp only [eqToHom_refl, Category.comp_id] at hP hQ
  obtain rfl : xP = yP := Subtype.ext hP
  obtain rfl : xQ = yQ := Subtype.ext hQ
  rfl

end WeierstrassCurve.DrinfeldGlobal.RawRepReduce

open WeierstrassCurve.DrinfeldGlobal.RawRepReduce in
set_option maxHeartbeats 3200000 in
theorem solution
    {A : Type u} [CommRing A] (q : ℕ) [Fact q.Prime]
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type u) [CommRing T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ), IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type u) [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T'),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ), IsCoefficientHom W f φ)
    (B : Type u) [CommRing B] [Algebra A B] (W : WeierstrassCurve B) (hΔ : IsUnit W.Δ) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra B C) (_ : IsScalarTower A B C)
      (_ : Module.Finite B C) (xᵤ : RawDrinfeldPair C)
      (_ : RawDrinfeldPair.IsLevel 𝒢 q (W.map (algebraMap B C)) xᵤ),
      ∀ (T : Type u) [CommRing T] [Algebra A T] (φ : B →ₐ[A] T) (x : RawDrinfeldPair T),
        RawDrinfeldPair.IsLevel 𝒢 q (W.map φ.toRingHom) x ↔
          ∃! ψ : C →ₐ[A] T, ψ.toRingHom.comp (algebraMap B C) = φ.toRingHom ∧ 𝒯.map ψ xᵤ = x := by
  classical

  haveI hWell : WeierstrassCurve.IsElliptic W := ⟨hΔ⟩
  set G : RelativeGroupLaw B (projModelStrCR W) := 𝒢 B W hΔ with hG
  obtain ⟨ev, hev⟩ := h𝒢 B W hΔ
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le

  obtain ⟨C, instC, instBC, instFin, Pu, Qu, hU, huniv⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_moduleFinite_represents_isDrinfeldBasisOver_of_two_le
      (W : WeierstrassCurve.Projective B) G ev (hG ▸ hev) q hq
  letI : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  haveI hAT : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

  set ι : B →ₐ[A] C := IsScalarTower.toAlgHom A B C with hι
  have hιr : ι.toRingHom = algebraMap B C := rfl
  obtain ⟨φc, hφc, hcoef⟩ := hCO B C W (algebraMap B C)
  have hK2 := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W (algebraMap B C) φc hφc hcoef
  let PuSec : Section (W.map (algebraMap B C)) :=
    ⟨hK2.lift Pu.1 (𝟙 _) (by simpa using Pu.2), hK2.lift_snd _ _ _⟩
  let QuSec : Section (W.map (algebraMap B C)) :=
    ⟨hK2.lift Qu.1 (𝟙 _) (by simpa using Qu.2), hK2.lift_snd _ _ _⟩
  have hPuSec : PuSec.1 ≫ Proj.map φc hφc = Pu.1 := hK2.lift_fst _ _ _
  have hQuSec : QuSec.1 ≫ Proj.map φc hφc = Qu.1 := hK2.lift_fst _ _ _
  let xᵤ : RawDrinfeldPair C := ⟨W.map (algebraMap B C), PuSec, QuSec⟩

  have hsqC : Proj.map φc hφc ≫ projModelStrCR W =
      projModelStrCR (W.map (algebraMap B C)) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := hK2.w
  have hPu' : (xᵤ.P.1 ≫ eqToHom (congrArg projModelCR (rfl : xᵤ.curve = W.map ι.toRingHom)) ≫ Proj.map φc hφc) ≫
      projModelStrCR W = Spec.map (CommRingCat.ofHom ι.toRingHom) := by
    simp only [eqToHom_refl, Category.id_comp, xᵤ, hPuSec]; exact Pu.2
  have hQu' : (xᵤ.Q.1 ≫ eqToHom (congrArg projModelCR (rfl : xᵤ.curve = W.map ι.toRingHom)) ≫ Proj.map φc hφc) ≫
      projModelStrCR W = Spec.map (CommRingCat.ofHom ι.toRingHom) := by
    simp only [eqToHom_refl, Category.id_comp, xᵤ, hQuSec]; exact Qu.2
  have hxᵤ : RawDrinfeldPair.IsLevel 𝒢 q (W.map (algebraMap B C)) xᵤ := by
    have h6 := WeierstrassCurve.DrinfeldGlobal.isLevel_iff_isDrinfeldBasisOver_comp_projMap q 𝒢 h𝒢O B W hΔ C ι
      φc hφc hcoef hsqC xᵤ rfl hPu' hQu'
    refine h6.mpr ?_
    have ePu : (xᵤ.P.1 ≫ eqToHom (congrArg projModelCR (rfl : xᵤ.curve = W.map ι.toRingHom)) ≫ Proj.map φc hφc) = Pu.1 := by
      simp only [eqToHom_refl, Category.id_comp, xᵤ, hPuSec]
    have eQu : (xᵤ.Q.1 ≫ eqToHom (congrArg projModelCR (rfl : xᵤ.curve = W.map ι.toRingHom)) ≫ Proj.map φc hφc) = Qu.1 := by
      simp only [eqToHom_refl, Category.id_comp, xᵤ, hQuSec]
    convert hU using 2 <;> first | exact ePu | exact eQu | (rw [hιr]) | (simp only [hιr]) | rfl
  refine ⟨C, instC, inferInstance, instBC, hAT, instFin, xᵤ, hxᵤ, ?_⟩

  intro T _ _ φ x
  obtain ⟨xc, xP, xQ⟩ := x
  letI instBT : Algebra B T := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq (fun a ↦ (φ.commutes a).symm)
  have hφalg : algebraMap B T = φ.toRingHom := rfl
  obtain ⟨φcT, hφcT, hcoefT⟩ := hCO B T W φ.toRingHom
  have hK2T := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W φ.toRingHom φcT hφcT hcoefT
  have hsqT : Proj.map φcT hφcT ≫ projModelStrCR W =
      projModelStrCR (W.map φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := hK2T.w

  have push_over : ∀ (s : Section (W.map φ.toRingHom)),
      (s.1 ≫ Proj.map φcT hφcT) ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom (algebraMap B T)) := by
    intro s; rw [Category.assoc, hsqT, ← Category.assoc, s.2, Category.id_comp]

  have transport : ∀ (ψ : C →ₐ[A] T), ψ.toRingHom.comp (algebraMap B C) = φ.toRingHom →
      ∃ hc' : (𝒯.map ψ xᵤ).curve = W.map φ.toRingHom,
        (𝒯.map ψ xᵤ).P.1 ≫ eqToHom (congrArg projModelCR hc') ≫ Proj.map φcT hφcT =
          Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Pu.1 ∧
        (𝒯.map ψ xᵤ).Q.1 ≫ eqToHom (congrArg projModelCR hc') ≫ Proj.map φcT hφcT =
          Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Qu.1 := by
    intro ψ hψ
    obtain ⟨hc', hmap⟩ := h𝒯.2 C T ψ xᵤ
    obtain ⟨φcψ, hφcψ, hcoefψ⟩ := hCO C T (W.map (algebraMap B C)) ψ.toRingHom
    obtain ⟨hP, hQ⟩ := hmap φcψ hφcψ hcoefψ
    have e : (W.map (algebraMap B C)).map ψ.toRingHom = W.map φ.toRingHom := by
      rw [WeierstrassCurve.map_map, hψ]

    have hcomp : Proj.map (φcψ.comp φc) (HomogeneousIdeal.irrelevant_le_map_comp hφc hφcψ) =
        eqToHom (congrArg projModelCR e) ≫ Proj.map φcT hφcT := by
      refine projMap_eq_eqToHom_comp_projMap W φ.toRingHom e _ _ _ _ ?_ ?_ hcoefT.1 hcoefT.2
      · intro a
        rw [GradedRingHom.comp_apply, hcoef.1 a]
        exact (hcoefψ.1 (algebraMap B C a)).trans (by rw [← hψ]; rfl)
      · intro i
        rw [GradedRingHom.comp_apply, hcoef.2 i]
        exact hcoefψ.2 i
    refine ⟨hc'.trans e, ?_, ?_⟩
    · calc (𝒯.map ψ xᵤ).P.1 ≫ eqToHom (congrArg projModelCR (hc'.trans e)) ≫ Proj.map φcT hφcT
          = (𝒯.map ψ xᵤ).P.1 ≫ eqToHom (congrArg projModelCR hc') ≫
              (eqToHom (congrArg projModelCR e) ≫ Proj.map φcT hφcT) := by
            simp
        _ = (𝒯.map ψ xᵤ).P.1 ≫ eqToHom (congrArg projModelCR hc') ≫ Proj.map φcψ hφcψ ≫ Proj.map φc hφc := by
            rw [← hcomp, Proj.map_comp]
        _ = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Pu.1 := by
            rw [reassoc_of% hP]
            congr 1
    · calc (𝒯.map ψ xᵤ).Q.1 ≫ eqToHom (congrArg projModelCR (hc'.trans e)) ≫ Proj.map φcT hφcT
          = (𝒯.map ψ xᵤ).Q.1 ≫ eqToHom (congrArg projModelCR hc') ≫
              (eqToHom (congrArg projModelCR e) ≫ Proj.map φcT hφcT) := by
            simp
        _ = (𝒯.map ψ xᵤ).Q.1 ≫ eqToHom (congrArg projModelCR hc') ≫ Proj.map φcψ hφcψ ≫ Proj.map φc hφc := by
            rw [← hcomp, Proj.map_comp]
        _ = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Qu.1 := by
            rw [reassoc_of% hQ]
            congr 1

  have transport_read : ∀ (sP sQ : Section (W.map φ.toRingHom)) (ψ : C →ₐ[A] T),
      ψ.toRingHom.comp (algebraMap B C) = φ.toRingHom →
      𝒯.map ψ xᵤ = ⟨W.map φ.toRingHom, sP, sQ⟩ →
      sP.1 ≫ Proj.map φcT hφcT = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Pu.1 ∧
      sQ.1 ≫ Proj.map φcT hφcT = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Qu.1 := by
    intro sP sQ ψ hψ hmap
    have key : ∀ y : RawDrinfeldPair T, y = ⟨W.map φ.toRingHom, sP, sQ⟩ →
        (∃ hc' : y.curve = W.map φ.toRingHom,
          y.P.1 ≫ eqToHom (congrArg projModelCR hc') ≫ Proj.map φcT hφcT =
            Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Pu.1 ∧
          y.Q.1 ≫ eqToHom (congrArg projModelCR hc') ≫ Proj.map φcT hφcT =
            Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Qu.1) →
        sP.1 ≫ Proj.map φcT hφcT = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Pu.1 ∧
        sQ.1 ≫ Proj.map φcT hφcT = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Qu.1 := by
      rintro _ rfl ⟨hc', h1, h2⟩
      simp only [eqToHom_refl, Category.id_comp] at h1 h2
      exact ⟨h1, h2⟩
    exact key _ hmap (transport ψ hψ)
  constructor
  ·
    rintro ⟨hc, hlev⟩
    subst hc
    have hxP : (xP.1 ≫ eqToHom (congrArg projModelCR (rfl : (W.map φ.toRingHom : WeierstrassCurve.Projective T) =
        W.map φ.toRingHom)) ≫ Proj.map φcT hφcT) ≫ projModelStrCR W =
        Spec.map (CommRingCat.ofHom φ.toRingHom) := by
      (first | exact push_over xP | simpa using push_over xP | (have h__ := push_over xP; simp at h__; exact h__))
    have hxQ : (xQ.1 ≫ eqToHom (congrArg projModelCR (rfl : (W.map φ.toRingHom : WeierstrassCurve.Projective T) =
        W.map φ.toRingHom)) ≫ Proj.map φcT hφcT) ≫ projModelStrCR W =
        Spec.map (CommRingCat.ofHom φ.toRingHom) := by
      (first | exact push_over xQ | simpa using push_over xQ | (have h__ := push_over xQ; simp at h__; exact h__))
    have h6 := WeierstrassCurve.DrinfeldGlobal.isLevel_iff_isDrinfeldBasisOver_comp_projMap q 𝒢 h𝒢O B W hΔ T φ
      φcT hφcT hcoefT hsqT ⟨W.map φ.toRingHom, xP, xQ⟩ rfl hxP hxQ
    have hDr := h6.mp ⟨rfl, hlev⟩
    obtain ⟨ψ₀, ⟨hψ₀P, hψ₀Q⟩, hψ₀uniq⟩ := (huniv T _ _).mp hDr
    simp only [eqToHom_refl, Category.id_comp] at hψ₀P hψ₀Q hψ₀uniq
    let ψ : C →ₐ[A] T := ψ₀.restrictScalars A
    have hψr : ψ.toRingHom = ψ₀.toRingHom := rfl
    have hψcomp : ψ.toRingHom.comp (algebraMap B C) = φ.toRingHom := ψ₀.comp_algebraMap
    have hmapψ : 𝒯.map ψ xᵤ = ⟨W.map φ.toRingHom, xP, xQ⟩ := by
      obtain ⟨hc', hP', hQ'⟩ := transport ψ hψcomp
      refine rawDrinfeldPair_ext _ _ hc' ?_ ?_
      · apply hK2T.hom_ext
        · rw [Category.assoc, hP', hψr, hψ₀P]
        · rw [Category.assoc, eqToHom_comp_projModelStrCR hc', (𝒯.map ψ xᵤ).P.2]
          exact xP.2.symm
      · apply hK2T.hom_ext
        · rw [Category.assoc, hQ', hψr, hψ₀Q]
        · rw [Category.assoc, eqToHom_comp_projModelStrCR hc', (𝒯.map ψ xᵤ).Q.2]
          exact xQ.2.symm
    refine ⟨ψ, ⟨hψcomp, hmapψ⟩, ?_⟩

    rintro ψ' ⟨hψ'comp, hmap'⟩
    obtain ⟨h1, h2⟩ := transport_read xP xQ ψ' hψ'comp hmap'
    let ψ'₀ : C →ₐ[B] T :=
      { toRingHom := ψ'.toRingHom
        commutes' := fun b ↦ by
          show ψ'.toRingHom (algebraMap B C b) = φ.toRingHom b
          exact RingHom.congr_fun hψ'comp b }
    have hψ'₀ : ψ'₀ = ψ₀ := hψ₀uniq ψ'₀ ⟨h1.symm, h2.symm⟩
    apply AlgHom.ext
    intro c
    exact (AlgHom.congr_fun hψ'₀ c : _)
  ·
    rintro ⟨ψ, ⟨hψcomp, hmap⟩, -⟩
    have h := 𝒯.isLevel_map ψ (W.map (algebraMap B C)) xᵤ hxᵤ
    rw [hmap, WeierstrassCurve.map_map, hψcomp] at h
    exact h

end S_WeierstrassCurve_DrinfeldGlobal_exists_moduleFinite_represents_isLevel
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_moduleFinite_represents_isLevel (solution)
