-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.isReduced_schemeKer_of_isPointsEval_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/247ef940-5ea4-52ae-beca-4b679e161d99

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_etale_of_isClosedImmersion_of_nsmul_eq_one_of_isUnit
import Theorems.Thm_WeierstrassProjModel_isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic
import Theorems.Thm_AlgebraicGeometry_isReduced_of_flat_of_formallyUnramified_of_isIntegral
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_isCommutative_of_isElliptic_of_baseChangeIso_of_isDomain
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_isReduced_schemeKer_of_isPointsEval_of_isUnit
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false
set_option linter.unusedVariables false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal"

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace KTRing
namespace TorsionReduced

def toGRJ {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : WeierstrassProjModel.RelativeGroupLaw R f) : GoodReductionJacobian.RelativeGroupLaw R f where
  mul := G.mul
  one := G.one
  inv := G.inv
  mul_assoc := G.mul_assoc
  one_mul := G.one_mul
  mul_one := G.mul_one
  inv_mul_cancel := G.inv_mul_cancel
  mul_natural := G.mul_natural

theorem toGRJ_nsmul {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : WeierstrassProjModel.RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : (toGRJ G).nsmul t n x = G.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (toGRJ G).mul t ((toGRJ G).nsmul t n x) x = G.mul t (G.nsmul t n x) x
    rw [ih]; rfl

theorem toGRJ_schemeNsmul {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : WeierstrassProjModel.RelativeGroupLaw R f) (n : ℕ) : (toGRJ G).schemeNsmul n = G.schemeNsmul n := by
  show ((toGRJ G).nsmul f n _).1 = (G.nsmul f n _).1
  rw [toGRJ_nsmul]

end KTRing.TorsionReduced

open KTRing.TorsionReduced in
theorem solution {B : Type} [CommRing B] [IsDomain B] (V : WeierstrassCurve.Projective B)
    [V.toAffine.IsElliptic] (G : RelativeGroupLaw B (projModelStrCR V))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra B F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) {n : ℕ} (hn : IsUnit ((n : ℕ) : B)) (hn0 : 0 < n) :
    IsReduced (G.schemeKer n) := by

  obtain ⟨-, hflat, hlfp⟩ := WeierstrassProjModel.isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic V G ev hev hn0

  have hbc : ∀ (K : Type) [Field K] [Algebra B K],
      Nonempty (pullback (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap B K))) ≅
        projModelCR (V.baseChange K)) := by
    intro K _ _
    obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom V (algebraMap B K)
    exact ⟨(isPullback_projMap_of_isCoefficientHom V (algebraMap B K) φ hφ hcoef).isoPullback.symm⟩
  have hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (x y : SchemeHomOver t (projModelStrCR V)),
      G.mul t x y = G.mul t y x := fun t x y =>
    WeierstrassProjModel.RelativeGroupLaw.isCommutative_of_isElliptic_of_baseChangeIso_of_isDomain V hbc G t x y

  haveI : IsProper (projModelStrCR V) := WeierstrassProjModel.projModelStrCR_isProper V
  set i : G.schemeKer n ⟶ projModelCR V := pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 with hi_def
  have hi : i ≫ projModelStrCR V = G.schemeKerStr n := by
    have h1 : i ≫ projModelStrCR V = i ≫ (G.schemeNsmul n ≫ projModelStrCR V) := by rw [G.schemeNsmul_over]
    rw [h1, ← Category.assoc, hi_def, pullback.condition, Category.assoc, (G.one (𝟙 _)).2, Category.comp_id]
  haveI hone_ci : IsClosedImmersion (G.one (𝟙 (Spec (CommRingCat.of B)))).1 := by
    have : IsClosedImmersion ((G.one (𝟙 (Spec (CommRingCat.of B)))).1 ≫ projModelStrCR V) := by
      rw [(G.one (𝟙 _)).2]; infer_instance
    exact IsClosedImmersion.of_comp _ (projModelStrCR V)
  haveI : IsClosedImmersion i := by rw [hi_def]; infer_instance
  haveI : Flat (i ≫ projModelStrCR V) := by rw [hi]; exact hflat
  haveI : LocallyOfFinitePresentation (i ≫ projModelStrCR V) := by rw [hi]; exact hlfp

  have hψ : pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ 𝟙 (Spec (CommRingCat.of B)) = i ≫ projModelStrCR V := by
    rw [Category.comp_id, hi]
  have htorsW : G.nsmul (i ≫ projModelStrCR V) n ⟨i, rfl⟩ = G.one (i ≫ projModelStrCR V) := by
    have hid : schemeHomOverComp i rfl (RelativeGroupLaw.idPoint (f := projModelStrCR V)) =
        (⟨i, rfl⟩ : SchemeHomOver (i ≫ projModelStrCR V) (projModelStrCR V)) :=
      Subtype.ext (Category.comp_id i)
    have hnat := G.nsmul_natural (projModelStrCR V) (i ≫ projModelStrCR V) i rfl n RelativeGroupLaw.idPoint
    rw [hid] at hnat
    rw [← hnat, ← G.one_natural (𝟙 _) (i ≫ projModelStrCR V) (pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1) hψ]
    apply Subtype.ext
    rw [schemeHomOverComp_coe, schemeHomOverComp_coe]
    show i ≫ G.schemeNsmul n = _
    rw [hi_def, pullback.condition]
  have htors : (toGRJ G).nsmul (i ≫ projModelStrCR V) n ⟨i, rfl⟩ = (toGRJ G).one (i ≫ projModelStrCR V) := by
    rw [toGRJ_nsmul]; exact htorsW

  have het := (GoodReductionJacobian.RelativeGroupLaw.etale_of_isClosedImmersion_of_nsmul_eq_one_of_isUnit
    (toGRJ G) (fun t x y => hcomm t x y) n hn i htors).1
  haveI : Etale (i ≫ projModelStrCR V) := het
  haveI : LocallyOfFiniteType (i ≫ projModelStrCR V) := inferInstance

  exact AlgebraicGeometry.isReduced_of_flat_of_formallyUnramified_of_isIntegral (i ≫ projModelStrCR V)

end

end S_WeierstrassProjModel_RelativeGroupLaw_isReduced_schemeKer_of_isPointsEval_of_isUnit
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_isReduced_schemeKer_of_isPointsEval_of_isUnit (solution)
