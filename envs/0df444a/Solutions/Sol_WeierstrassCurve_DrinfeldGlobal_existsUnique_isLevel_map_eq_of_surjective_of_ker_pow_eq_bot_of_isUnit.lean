-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/04a05f3b-4b16-5ccf-bcd3-eeb23479abdd

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_PointChart
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit_of_ne_two
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_isDrinfeldBasisOver_id
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_two_eq_one_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_isUnit_sub_of_isSectionThrough_of_two
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_two_of_isSectionThrough_of_isUnit_sub
import Theorems.Thm_WeierstrassCurve_existsUnique_equation_two_torsion_map_eq_of_surjective_of_ker_pow_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

p2m_open "ModularCurve WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit.WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing"

attribute [local instance] MvPolynomial.gradedAlgebra

set_option autoImplicit false

p2m_open "ModularCurve WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit.WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing"

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.unusedVariables false

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra~schemeHomOverComp"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "mk.injEq a₃ a₁ map mk reduction toAffine Δ Projective DrinfeldGlobal.existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit_of_ne_two existsUnique_equation_two_torsion_map_eq_of_surjective_of_ker_pow_eq_bot"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "base Section IsDrinfeldBasis RawDrinfeldPair GroupLaws RawDrinfeldPair.IsLevel LevelTransport IsSectionThrough existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit_of_ne_two RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit isSectionThrough_map_of_isSectionTransport isDrinfeldBasis_iff_isDrinfeldBasisOver_id equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough nsmul_two_eq_one_iff_of_isSectionThrough RawDrinfeldPair.IsLevel.isUnit_sub_of_isSectionThrough_of_two isDrinfeldBasis_two_of_isSectionThrough_of_isUnit_sub"
namespace DrinfeldLiftTwo
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

section Torsion

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem val_nsmul (G : RelativeGroupLaw R f) {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  conv_lhs => rw [← hx]
  rw [← G.nsmul_natural f t x.1 x.2 n]
  rfl

end Torsion

theorem nsmul_eq_one_of_comp_fst_eq {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (S : Section W)
    (r : base (T := T) ⟶ G.schemeKer q)
    (hr : r ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 = S.1) :
    G.nsmul (𝟙 _) q S = G.one (𝟙 _) := by
  have hr1 : r ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1 = 𝟙 _ := by
    calc r ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1
        = (r ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1) ≫
            ((G.one (𝟙 _)).1 ≫ projModelStrCR W) := by
          rw [(G.one (𝟙 _)).2, Category.comp_id]
      _ = r ≫ (pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1 ≫ (G.one (𝟙 _)).1) ≫ projModelStrCR W := by
          simp only [Category.assoc]
      _ = r ≫ (pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 ≫ G.schemeNsmul q) ≫ projModelStrCR W := by
          rw [pullback.condition]
      _ = (r ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1) ≫ (G.schemeNsmul q ≫ projModelStrCR W) := by
          simp only [Category.assoc]
      _ = 𝟙 _ := by rw [hr, G.schemeNsmul_over, S.2]
  apply Subtype.ext
  rw [val_nsmul, ← hr, Category.assoc, pullback.condition, ← Category.assoc, hr1, Category.id_comp]

theorem nsmul_eq_one_of_isDrinfeldBasis {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) {q : ℕ} (hq : 2 ≤ q) {P Q : Section W}
    (h : IsDrinfeldBasis G q P Q) :
    G.nsmul (𝟙 _) q P = G.one (𝟙 _) ∧ G.nsmul (𝟙 _) q Q = G.one (𝟙 _) := by
  have h' := (isDrinfeldBasis_iff_isDrinfeldBasisOver_id G q P Q).mp h
  obtain ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩ := RelativeGroupLaw.IsDrinfeldBasisOver.exists_comp_fst_schemeKer_eq G hq h'
  exact ⟨nsmul_eq_one_of_comp_fst_eq G q P p hp, nsmul_eq_one_of_comp_fst_eq G q Q p' hp'⟩

section Through

variable {T : Type} [CommRing T]

theorem coords_unique {W : WeierstrassCurve.Projective T} {S : Section W} {x y x' y' : T}
    (h : IsSectionThrough S x y) (h' : IsSectionThrough S x' y') : x = x' ∧ y = y' :=
  ((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).2 S S x y x' y' h h').mp rfl

theorem section_unique {W : WeierstrassCurve.Projective T} {S S' : Section W} {x y : T}
    (h : IsSectionThrough S x y) (h' : IsSectionThrough S' x y) : S = S' :=
  ((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).2 S S' x y x y h h').mpr ⟨rfl, rfl⟩

def sectionThrough (W : WeierstrassCurve.Projective T) (x y : T) (h : W.toAffine.Equation x y) : Section W :=
  (((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x y).mp h).choose

theorem sectionThrough_spec (W : WeierstrassCurve.Projective T) (x y : T) (h : W.toAffine.Equation x y) :
    IsSectionThrough (sectionThrough W x y h) x y :=
  (((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x y).mp h).choose_spec

theorem equation_of_isSectionThrough {W : WeierstrassCurve.Projective T} {S : Section W} {x y : T}
    (h : IsSectionThrough S x y) : W.toAffine.Equation x y :=
  ((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x y).mpr ⟨S, h⟩

end Through

theorem isUnit_of_isUnit_map {T T' : Type} [CommRing T] [CommRing T'] (π : T →+* T')
    (hπ : Function.Surjective π) (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥) (a : T) (ha : IsUnit (π a)) :
    IsUnit a := by
  obtain ⟨n, hn⟩ := hnil
  obtain ⟨u, hu⟩ := ha
  obtain ⟨b, hb⟩ := hπ ((u⁻¹ : T'ˣ) : T')
  have hmem : a * b - 1 ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hb, ← hu, Units.mul_inv, sub_self]
  have hnilp : IsNilpotent (a * b - 1) := by
    refine ⟨n, ?_⟩
    have h1 : (a * b - 1) ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hmem n
    rw [hn] at h1
    exact (Submodule.mem_bot _).mp h1
  have hab : IsUnit (a * b) := by
    have := hnilp.isUnit_add_one
    rwa [sub_add_cancel] at this
  exact isUnit_of_mul_isUnit_left hab

theorem main (A₀ : Type) [CommRing A₀]
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 2) (h𝒯 : 𝒯.IsSectionTransport)
    {T T' : Type} [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T']
    (π : T →ₐ[A₀] T') (hπ : Function.Surjective π) (hnil : ∃ n : ℕ, RingHom.ker π.toRingHom ^ n = ⊥)
    (E : WeierstrassCurve T) (hΔ : IsUnit E.Δ) (hq : IsUnit ((2 : ℕ) : T))
    (x' : RawDrinfeldPair T') (hx' : RawDrinfeldPair.IsLevel 𝒢 2 (E.map π.toRingHom) x') :
    ∃! x : RawDrinfeldPair T, RawDrinfeldPair.IsLevel 𝒢 2 E x ∧ 𝒯.map π x = x' := by
  classical
  have hq' : IsUnit ((2 : ℕ) : T') := by
    have h := hq.map π.toRingHom
    rwa [map_natCast] at h
  obtain ⟨C', P', Q'⟩ := x'
  obtain ⟨hc', hΔx', hDB'⟩ := hx'
  dsimp only at hc'
  subst hc'

  obtain ⟨⟨xP', yP', hP'⟩, ⟨xQ', yQ', hQ'⟩⟩ :=
    RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit 2 A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 (E.map π.toRingHom) hq'
      ⟨E.map π.toRingHom, P', Q'⟩ ⟨rfl, hΔx', hDB'⟩
  dsimp only at hP' hQ' hΔx' hDB'

  have htors' := nsmul_eq_one_of_isDrinfeldBasis (𝒢 T' (E.map π.toRingHom) hΔx') le_rfl hDB'
  have h2P' : 2 * yP' + (E.map π.toRingHom).a₁ * xP' + (E.map π.toRingHom).a₃ = 0 :=
    (nsmul_two_eq_one_iff_of_isSectionThrough 𝒢 h𝒢 h𝒢O T' hq' (E.map π.toRingHom) hΔx' P' xP' yP' hP').mp
      htors'.1
  have h2Q' : 2 * yQ' + (E.map π.toRingHom).a₁ * xQ' + (E.map π.toRingHom).a₃ = 0 :=
    (nsmul_two_eq_one_iff_of_isSectionThrough 𝒢 h𝒢 h𝒢O T' hq' (E.map π.toRingHom) hΔx' Q' xQ' yQ' hQ').mp
      htors'.2
  have hPE' : (E.map π.toRingHom).toAffine.Equation xP' yP' := equation_of_isSectionThrough hP'
  have hQE' : (E.map π.toRingHom).toAffine.Equation xQ' yQ' := equation_of_isSectionThrough hQ'

  obtain ⟨PP, hPP, huP⟩ :=
    WeierstrassCurve.existsUnique_equation_two_torsion_map_eq_of_surjective_of_ker_pow_eq_bot
      π.toRingHom hπ hnil E hΔ hq xP' yP' hPE' h2P'
  obtain ⟨QQ, hQQ, huQ⟩ :=
    WeierstrassCurve.existsUnique_equation_two_torsion_map_eq_of_surjective_of_ker_pow_eq_bot
      π.toRingHom hπ hnil E hΔ hq xQ' yQ' hQE' h2Q'
  obtain ⟨xP, yP⟩ := PP
  obtain ⟨xQ, yQ⟩ := QQ
  obtain ⟨⟨hπxP, hπyP⟩, hPE, h2P⟩ := hPP
  obtain ⟨⟨hπxQ, hπyQ⟩, hQE, h2Q⟩ := hQQ
  dsimp only at hπxP hπyP hPE h2P hπxQ hπyQ hQE h2Q

  have hind' : IsUnit (xP' - xQ') :=
    RawDrinfeldPair.IsLevel.isUnit_sub_of_isSectionThrough_of_two A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 (E.map π.toRingHom) hq'
      ⟨E.map π.toRingHom, P', Q'⟩ ⟨rfl, hΔx', hDB'⟩ xP' yP' xQ' yQ' hP' hQ'
  have hind : IsUnit (xP - xQ) := by
    refine isUnit_of_isUnit_map π.toRingHom hπ hnil (xP - xQ) ?_
    rw [map_sub]
    show IsUnit (π xP - π xQ)
    rw [show π xP = xP' from hπxP, show π xQ = xQ' from hπxQ]
    exact hind'

  let S : Section (E : WeierstrassCurve.Projective T) := sectionThrough E xP yP hPE
  let S' : Section (E : WeierstrassCurve.Projective T) := sectionThrough E xQ yQ hQE
  have hS : IsSectionThrough S xP yP := sectionThrough_spec E xP yP hPE
  have hS' : IsSectionThrough S' xQ yQ := sectionThrough_spec E xQ yQ hQE
  have hDB : IsDrinfeldBasis (𝒢 T E hΔ) 2 S S' :=
    isDrinfeldBasis_two_of_isSectionThrough_of_isUnit_sub 𝒢 h𝒢 h𝒢O hq E hΔ xP yP xQ yQ hPE hQE h2P h2Q hind
      S S' hS hS'
  let x : RawDrinfeldPair T := ⟨E, S, S'⟩
  have hx : RawDrinfeldPair.IsLevel 𝒢 2 E x := ⟨rfl, hΔ, hDB⟩
  refine ⟨x, ⟨hx, ?_⟩, ?_⟩
  ·
    have hCO := WeierstrassProjModel.exists_isCoefficientHom x.curve π.toRingHom
    obtain ⟨hPm, hQm⟩ := isSectionThrough_map_of_isSectionTransport A₀ 𝒢 2 𝒯 h𝒯 π x hCO ⟨xP, yP, xQ, yQ⟩ hS hS'
    have hcm : (𝒯.map π x).curve = E.map π.toRingHom := (𝒯.isLevel_map π E x hx).1
    dsimp only at hPm hQm
    rw [show π xP = xP' from hπxP, show π yP = yP' from hπyP] at hPm
    rw [show π xQ = xQ' from hπxQ, show π yQ = yQ' from hπyQ] at hQm
    revert hPm hQm hcm
    generalize 𝒯.map π x = m
    intro hPm hQm hcm
    obtain ⟨Cm, Pm, Qm⟩ := m
    dsimp only at hPm hQm hcm
    subst hcm
    obtain rfl := section_unique hPm hP'
    obtain rfl := section_unique hQm hQ'
    rfl
  ·
    rintro ⟨C₁, P₁, Q₁⟩ ⟨⟨hc₁, hΔ₁, hDB₁⟩, hx₁m⟩
    dsimp only at hc₁
    subst C₁
    dsimp only at hΔ₁ hDB₁
    obtain ⟨⟨x₁P, y₁P, h₁P⟩, ⟨x₁Q, y₁Q, h₁Q⟩⟩ :=
      RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit 2 A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 E hq ⟨E, P₁, Q₁⟩
        ⟨rfl, hΔ₁, hDB₁⟩
    dsimp only at h₁P h₁Q
    have htors₁ := nsmul_eq_one_of_isDrinfeldBasis (𝒢 T E hΔ₁) le_rfl hDB₁
    have h2P₁ : 2 * y₁P + E.a₁ * x₁P + E.a₃ = 0 :=
      (nsmul_two_eq_one_iff_of_isSectionThrough 𝒢 h𝒢 h𝒢O T hq E hΔ₁ P₁ x₁P y₁P h₁P).mp htors₁.1
    have h2Q₁ : 2 * y₁Q + E.a₁ * x₁Q + E.a₃ = 0 :=
      (nsmul_two_eq_one_iff_of_isSectionThrough 𝒢 h𝒢 h𝒢O T hq E hΔ₁ Q₁ x₁Q y₁Q h₁Q).mp htors₁.2
    have hPE₁ : E.toAffine.Equation x₁P y₁P := equation_of_isSectionThrough h₁P
    have hQE₁ : E.toAffine.Equation x₁Q y₁Q := equation_of_isSectionThrough h₁Q

    have hCO₁ := WeierstrassProjModel.exists_isCoefficientHom
      (⟨E, P₁, Q₁⟩ : RawDrinfeldPair T).curve π.toRingHom
    obtain ⟨hPm₁, hQm₁⟩ := isSectionThrough_map_of_isSectionTransport A₀ 𝒢 2 𝒯 h𝒯 π ⟨E, P₁, Q₁⟩ hCO₁
      ⟨x₁P, y₁P, x₁Q, y₁Q⟩ h₁P h₁Q
    dsimp only at hPm₁ hQm₁
    rw [hx₁m] at hPm₁ hQm₁
    dsimp only at hPm₁ hQm₁
    obtain ⟨e1, e2⟩ := coords_unique hPm₁ hP'
    obtain ⟨e3, e4⟩ := coords_unique hQm₁ hQ'
    have hP₁ : (x₁P, y₁P) = (xP, yP) := huP (x₁P, y₁P) ⟨⟨e1, e2⟩, hPE₁, h2P₁⟩
    have hQ₁ : (x₁Q, y₁Q) = (xQ, yQ) := huQ (x₁Q, y₁Q) ⟨⟨e3, e4⟩, hQE₁, h2Q₁⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ hP₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ hQ₁
    obtain rfl := section_unique h₁P hS
    obtain rfl := section_unique h₁Q hS'
    rfl

end WeierstrassCurve.DrinfeldGlobal.DrinfeldLiftTwo

end

theorem solution
    (q : ℕ) [Fact q.Prime] (A₀ : Type) [CommRing A₀]
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T T' : Type} [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T']
    (π : T →ₐ[A₀] T') (hπ : Function.Surjective π) (hnil : ∃ n : ℕ, RingHom.ker π.toRingHom ^ n = ⊥)
    (E : WeierstrassCurve T) (hΔ : IsUnit E.Δ) (hq : IsUnit ((q : ℕ) : T))
    (x' : RawDrinfeldPair T') (hx' : RawDrinfeldPair.IsLevel 𝒢 q (E.map π.toRingHom) x') :
    ∃! x : RawDrinfeldPair T, RawDrinfeldPair.IsLevel 𝒢 q E x ∧ 𝒯.map π x = x' := by
  by_cases hq2 : q = 2
  · subst hq2
    exact WeierstrassCurve.DrinfeldGlobal.DrinfeldLiftTwo.main A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 π hπ hnil E hΔ hq x' hx'
  · exact WeierstrassCurve.DrinfeldGlobal.existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit_of_ne_two
      q hq2 A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 π hπ hnil E hΔ hq x' hx'

end S_WeierstrassCurve_DrinfeldGlobal_existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit (solution)
