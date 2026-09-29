-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.natCard_rawDrinfeldPair_isLevel_two_eq_natCard_GL_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/afdbefc3-00d3-597c-8896-e3b716a9551d

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_nsmul_eq_one_and_nsmul_eq_one
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_two_eq_one_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_isUnit_sub_of_isSectionThrough_of_two
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_two_of_isSectionThrough_of_isUnit_sub
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_natCard_rawDrinfeldPair_isLevel_two_eq_natCard_GL_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.evalUniv_add GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

namespace DrinCount2

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

def Tor {Ω : Type} [Field Ω] (W : WeierstrassCurve Ω) (p : Ω × Ω) : Prop :=
  W.toAffine.Equation p.1 p.2 ∧ 2 * p.2 + W.a₁ * p.1 + W.a₃ = 0

theorem tor_iff {Ω : Type} [Field Ω] (W : WeierstrassCurve Ω) (h2 : (2 : Ω) ≠ 0) (x y : Ω) :
    Tor W (x, y) ↔ (W.Ψ₂Sq.eval x = 0 ∧ y = -(W.a₁ * x + W.a₃) / 2) := by
  have key := congrArg (Polynomial.evalEval x y) W.ψ₂_sq
  rw [Polynomial.evalEval_pow, Polynomial.evalEval_add, Polynomial.evalEval_mul, Polynomial.evalEval_C,
    WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY] at key
  have h4 : (4 : Polynomial (Polynomial Ω)).evalEval x y = 4 := by
    rw [show (4 : Polynomial (Polynomial Ω)) = ((4 : ℕ) : Polynomial (Polynomial Ω)) by norm_cast, Polynomial.evalEval_natCast]; norm_cast
  rw [h4] at key
  simp only [Tor]
  constructor
  · rintro ⟨hE, h2y⟩
    have hE' : W.toAffine.polynomial.evalEval x y = 0 := hE
    refine ⟨?_, ?_⟩
    · rw [h2y, hE'] at key; simpa using key.symm
    · field_simp; linear_combination h2y
  · rintro ⟨hr, hy⟩
    have h2y : 2 * y + W.a₁ * x + W.a₃ = 0 := by rw [hy]; field_simp; ring
    refine ⟨?_, h2y⟩
    show W.toAffine.polynomial.evalEval x y = 0
    rw [h2y, hr] at key
    have h4ne : (4 : Ω) ≠ 0 := by
      have : (4 : Ω) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    have : (4 : Ω) * W.toAffine.polynomial.evalEval x y = 0 := by linear_combination -key
    exact (mul_eq_zero.mp this).resolve_left h4ne

theorem card_roots_Ψ₂Sq {Ω : Type} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω)
    (h2 : (2 : Ω) ≠ 0) (hΔ : IsUnit W.Δ) : W.Ψ₂Sq.roots.toFinset.card = 3 := by
  have ha : W.twoTorsionPolynomial.a ≠ 0 := by
    show (4 : Ω) ≠ 0
    have : (4 : Ω) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hd : W.twoTorsionPolynomial.discr ≠ 0 :=
    W.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) hΔ
  have hs : (W.twoTorsionPolynomial.toPoly.map (RingHom.id Ω)).Splits := by
    rw [Polynomial.map_id]; exact IsAlgClosed.splits _
  have h := Cubic.card_roots_of_discr_ne_zero (φ := RingHom.id Ω) ha hs hd
  have hmap : Cubic.map (RingHom.id Ω) W.twoTorsionPolynomial = W.twoTorsionPolynomial := by
    cases W.twoTorsionPolynomial with | mk a b c d => rfl
  rw [WeierstrassCurve.Ψ₂Sq_eq]
  rw [hmap] at h
  exact h

theorem card_pairs {Ω : Type} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω)
    (h2 : (2 : Ω) ≠ 0) (hΔ : IsUnit W.Δ) :
    Nat.card {p : (Ω × Ω) × (Ω × Ω) // Tor W p.1 ∧ Tor W p.2 ∧ p.1.1 ≠ p.2.1} = 6 := by
  classical
  set R : Finset Ω := W.Ψ₂Sq.roots.toFinset with hR
  have hR3 : R.card = 3 := card_roots_Ψ₂Sq W h2 hΔ
  have hne : W.Ψ₂Sq ≠ 0 := by
    intro h0
    have := card_roots_Ψ₂Sq W h2 hΔ
    rw [h0, Polynomial.roots_zero] at this
    simp at this
  have hmem : ∀ x : Ω, x ∈ R ↔ W.Ψ₂Sq.eval x = 0 := by
    intro x; rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot]
  let f : Ω → Ω := fun x => -(W.a₁ * x + W.a₃) / 2
  have e : {p : (Ω × Ω) × (Ω × Ω) // Tor W p.1 ∧ Tor W p.2 ∧ p.1.1 ≠ p.2.1} ≃ ↥R.offDiag :=
    { toFun := fun p => ⟨(p.1.1.1, p.1.2.1), by
        rw [Finset.mem_offDiag, hmem, hmem]
        obtain ⟨h1, h2', h3⟩ := p.2
        exact ⟨((tor_iff W h2 _ _).mp h1).1, ((tor_iff W h2 _ _).mp h2').1, h3⟩⟩
      invFun := fun ab => ⟨((ab.1.1, f ab.1.1), (ab.1.2, f ab.1.2)), by
        have hab := Finset.mem_offDiag.mp ab.2
        rw [hmem, hmem] at hab
        exact ⟨(tor_iff W h2 _ _).mpr ⟨hab.1, rfl⟩, (tor_iff W h2 _ _).mpr ⟨hab.2.1, rfl⟩, hab.2.2⟩⟩
      left_inv := by
        rintro ⟨⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩, h1, h2', h3⟩
        have hy₁ := ((tor_iff W h2 _ _).mp h1).2
        have hy₂ := ((tor_iff W h2 _ _).mp h2').2
        apply Subtype.ext
        simp only [f]
        rw [← hy₁, ← hy₂]
      right_inv := by
        rintro ⟨⟨a, b⟩, hab⟩
        rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.offDiag_card, hR3]

theorem card_GL2_F2 : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

end DrinCount2

open WeierstrassCurve.DrinfeldGlobal

theorem solution
    (A : Type) [CommRing A]
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 2) (h𝒯 : 𝒯.IsSectionTransport)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A Ω] (hqΩ : ((2 : ℕ) : Ω) ≠ 0)
    (W₀ : WeierstrassCurve Ω) (hΔ : IsUnit W₀.Δ) :
    Nat.card {x : RawDrinfeldPair Ω // RawDrinfeldPair.IsLevel 𝒢 2 W₀ x} = Nat.card (GL (Fin 2) (ZMod 2)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2u : IsUnit ((2 : ℕ) : Ω) := isUnit_iff_ne_zero.mpr hqΩ
  have h2 : (2 : Ω) ≠ 0 := by exact_mod_cast hqΩ

  have hEU := WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W₀

  let sec : ∀ p : Ω × Ω, W₀.toAffine.Equation p.1 p.2 → Section W₀ := fun p h => ((hEU.1 p.1 p.2).mp h).choose
  have hsec : ∀ (p : Ω × Ω) (h : W₀.toAffine.Equation p.1 p.2), IsSectionThrough (sec p h) p.1 p.2 :=
    fun p h => ((hEU.1 p.1 p.2).mp h).choose_spec

  let Ψ : {p : (Ω × Ω) × (Ω × Ω) // DrinCount2.Tor W₀ p.1 ∧ DrinCount2.Tor W₀ p.2 ∧ p.1.1 ≠ p.2.1} →
      {x : RawDrinfeldPair Ω // RawDrinfeldPair.IsLevel 𝒢 2 W₀ x} := fun p =>
    ⟨⟨W₀, sec p.1.1 p.2.1.1, sec p.1.2 p.2.2.1.1⟩, rfl, hΔ,
      WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_two_of_isSectionThrough_of_isUnit_sub 𝒢 h𝒢 h𝒢O h2u W₀ hΔ
        p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2.1.1 p.2.2.1.1 p.2.1.2 p.2.2.1.2
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr p.2.2.2))
        (sec p.1.1 p.2.1.1) (sec p.1.2 p.2.2.1.1) (hsec p.1.1 p.2.1.1) (hsec p.1.2 p.2.2.1.1)⟩
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro p p' h
      have h1 := congrArg Subtype.val h
      simp only [Ψ, RawDrinfeldPair.mk.injEq, heq_eq_eq, true_and] at h1
      obtain ⟨hP, hQ⟩ := h1
      have e1 := (hEU.2 _ _ _ _ _ _ (hsec p.1.1 p.2.1.1) (hsec p'.1.1 p'.2.1.1)).mp hP
      have e2 := (hEU.2 _ _ _ _ _ _ (hsec p.1.2 p.2.2.1.1) (hsec p'.1.2 p'.2.2.1.1)).mp hQ
      apply Subtype.ext
      exact Prod.ext (Prod.ext e1.1 e1.2) (Prod.ext e2.1 e2.2)
    · rintro ⟨x, hx⟩
      obtain ⟨⟨xP, yP, hP⟩, ⟨xQ, yQ, hQ⟩⟩ :=
        WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit
          2 A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 W₀ h2u x hx
      have hPQ : xP ≠ xQ := sub_ne_zero.mp
        (WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.IsLevel.isUnit_sub_of_isSectionThrough_of_two
          A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 W₀ h2u x hx xP yP xQ yQ hP hQ).ne_zero
      obtain ⟨c, P, Q⟩ := x
      obtain ⟨hc, hΔ', hB⟩ := hx
      dsimp only at hc hΔ' hB hP hQ
      subst hc
      haveI : WeierstrassCurve.IsElliptic c := ⟨hΔ'⟩
      obtain ⟨hP2, hQ2⟩ := WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.nsmul_eq_one_and_nsmul_eq_one
        c (𝒢 Ω c hΔ') (h𝒢 Ω c hΔ') 2 P Q hB
      have h2P := (WeierstrassCurve.DrinfeldGlobal.nsmul_two_eq_one_iff_of_isSectionThrough 𝒢 h𝒢 h𝒢O Ω h2u c hΔ'
        P xP yP hP).mp hP2
      have h2Q := (WeierstrassCurve.DrinfeldGlobal.nsmul_two_eq_one_iff_of_isSectionThrough 𝒢 h𝒢 h𝒢O Ω h2u c hΔ'
        Q xQ yQ hQ).mp hQ2
      have hPE : c.toAffine.Equation xP yP := (hEU.1 xP yP).mpr ⟨P, hP⟩
      have hQE : c.toAffine.Equation xQ yQ := (hEU.1 xQ yQ).mpr ⟨Q, hQ⟩
      refine ⟨⟨((xP, yP), (xQ, yQ)), ⟨hPE, h2P⟩, ⟨hQE, h2Q⟩, hPQ⟩, ?_⟩
      apply Subtype.ext
      show (⟨c, sec (xP, yP) hPE, sec (xQ, yQ) hQE⟩ : RawDrinfeldPair Ω) = ⟨c, P, Q⟩
      have eP : sec (xP, yP) hPE = P := (hEU.2 _ _ _ _ _ _ (hsec (xP, yP) hPE) hP).mpr ⟨rfl, rfl⟩
      have eQ : sec (xQ, yQ) hQE = Q := (hEU.2 _ _ _ _ _ _ (hsec (xQ, yQ) hQE) hQ).mpr ⟨rfl, rfl⟩
      rw [eP, eQ]

  rw [← Nat.card_eq_of_bijective Ψ hΨ, DrinCount2.card_pairs W₀ h2 hΔ, DrinCount2.card_GL2_F2]

end S_WeierstrassCurve_DrinfeldGlobal_natCard_rawDrinfeldPair_isLevel_two_eq_natCard_GL_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_natCard_rawDrinfeldPair_isLevel_two_eq_natCard_GL_of_isAlgClosed (solution)
