-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_isUnit_inLineMulPoly_eq_C_mul_of_isSectionThrough_zsmulSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/255a81b0-f28e-5c8a-ace6-f46ff843f9f3

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps
import Theorems.Thm_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_ModularCurve_LevelP_TorsionPointRing_isReduced_of_isUnit
import Theorems.Thm_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq
import Theorems.Thm_ModularCurve_LevelP_isDomain_and_isIntegrallyClosed_univBase
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_phi
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isUnit_inLineMulPoly_eq_C_mul_of_isSectionThrough_zsmulSection
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve.LevelRelabelling Polynomial AlgebraicGeometry.Polynomial"
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace LinkRing

section Alg
variable {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T} (G : RelativeGroupLaw T (projModelStrCR W))

theorem nsmul_eq_pow (n : ℕ) (x : Section W) :
    letI := G.pointGroup (𝟙 _); G.nsmul (𝟙 _) n x = x ^ n := by
  letI := G.pointGroup (𝟙 _)
  induction n with
  | zero => rfl
  | succ n ih => rw [G.nsmul_succ, ih, pow_succ]; rfl

theorem zsmulSection_eq_zpow (n : ℤ) (x : Section W) :
    letI := G.pointGroup (𝟙 _); zsmulSection G n x = x ^ n := by
  letI := G.pointGroup (𝟙 _)
  cases n with
  | ofNat k =>
    show G.nsmul (𝟙 _) k x = x ^ ((k : ℕ) : ℤ)
    rw [nsmul_eq_pow, zpow_natCast]
  | negSucc k =>
    show G.inv (𝟙 _) (G.nsmul (𝟙 _) (k + 1) x) = x ^ (Int.negSucc k)
    rw [nsmul_eq_pow, zpow_negSucc]
    rfl

theorem zsmulSection_zsmulSection (S : Section W) (a b : ℤ) :
    zsmulSection G b (zsmulSection G a S) = zsmulSection G (a * b) S := by
  letI := G.pointGroup (𝟙 _)
  rw [zsmulSection_eq_zpow, zsmulSection_eq_zpow, zsmulSection_eq_zpow, zpow_mul]

theorem zsmulSection_eq_of_nsmul_eq_one (S : Section W) (ℓ : ℕ) (hℓ : G.nsmul (𝟙 _) ℓ S = G.one (𝟙 _))
    (a a' : ℤ) (h : (a : ZMod ℓ) = (a' : ZMod ℓ)) : zsmulSection G a S = zsmulSection G a' S := by
  letI := G.pointGroup (𝟙 _)
  have hS : S ^ (ℓ : ℤ) = 1 := by rw [zpow_natCast, ← nsmul_eq_pow]; exact hℓ
  rw [zsmulSection_eq_zpow, zsmulSection_eq_zpow]
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a' a ℓ).mp h.symm
  have : a = a' + ℓ * k := by linarith
  rw [this, zpow_add, zpow_mul, hS, one_zpow, mul_one]

theorem nsmul_zsmulSection_eq_one (S : Section W) (ℓ : ℕ) (hS : G.nsmul (𝟙 _) ℓ S = G.one (𝟙 _)) (a : ℤ) :
    G.nsmul (𝟙 _) ℓ (zsmulSection G a S) = G.one (𝟙 _) := by
  letI := G.pointGroup (𝟙 _)
  have hS' : S ^ (ℓ : ℤ) = 1 := by rw [zpow_natCast, ← nsmul_eq_pow]; exact hS
  rw [nsmul_eq_pow, zsmulSection_eq_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hS', one_zpow]
  rfl

theorem zsmulSection_eq_of_one_eq [W.toAffine.IsElliptic] (G₀ G₁ : RelativeGroupLaw T (projModelStrCR W))
    (h1 : (G₀.one (𝟙 _)).1 = (G₁.one (𝟙 _)).1) (n : ℤ) (S : Section W) :
    zsmulSection G₀ n S = zsmulSection G₁ n S := by
  have hmul : ∀ x y : Section W, G₀.mul (𝟙 _) x y = G₁.mul (𝟙 _) x y :=
    fun x y => WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic W G₀ G₁ h1 (𝟙 _) x y
  have hone : G₀.one (𝟙 _) = G₁.one (𝟙 _) := Subtype.ext h1
  have hinv : ∀ x : Section W, G₀.inv (𝟙 _) x = G₁.inv (𝟙 _) x := by
    intro x
    have A1 : G₀.mul (𝟙 _) (G₀.inv (𝟙 _) x) x = G₀.one (𝟙 _) := by
      letI := G₀.pointGroup (𝟙 _); exact inv_mul_cancel x
    have A2 : ∀ p q r : Section W, G₀.mul (𝟙 _) (G₀.mul (𝟙 _) p q) r = G₀.mul (𝟙 _) p (G₀.mul (𝟙 _) q r) := by
      letI := G₀.pointGroup (𝟙 _); exact fun p q r => mul_assoc p q r
    have A3 : ∀ p : Section W, G₀.mul (𝟙 _) p (G₀.one (𝟙 _)) = p := by
      letI := G₀.pointGroup (𝟙 _); exact fun p => mul_one p
    have A4 : ∀ p : Section W, G₀.mul (𝟙 _) (G₀.one (𝟙 _)) p = p := by
      letI := G₀.pointGroup (𝟙 _); exact fun p => one_mul p
    have B1 : G₁.mul (𝟙 _) x (G₁.inv (𝟙 _) x) = G₁.one (𝟙 _) := by
      letI := G₁.pointGroup (𝟙 _); exact mul_inv_cancel x
    calc G₀.inv (𝟙 _) x = G₀.mul (𝟙 _) (G₀.inv (𝟙 _) x) (G₀.one (𝟙 _)) := (A3 _).symm
      _ = G₀.mul (𝟙 _) (G₀.inv (𝟙 _) x) (G₀.mul (𝟙 _) x (G₁.inv (𝟙 _) x)) := by rw [hone, ← B1, hmul x]
      _ = G₁.inv (𝟙 _) x := by rw [← A2, A1, A4]
  have hns : ∀ k : ℕ, G₀.nsmul (𝟙 _) k S = G₁.nsmul (𝟙 _) k S := by
    intro k
    induction k with
    | zero => exact hone
    | succ k ih => rw [G₀.nsmul_succ, G₁.nsmul_succ, ih, hmul]
  cases n with
  | ofNat k => exact hns k
  | negSucc k =>
    show G₀.inv (𝟙 _) (G₀.nsmul (𝟙 _) (k + 1) S) = G₁.inv (𝟙 _) (G₁.nsmul (𝟙 _) (k + 1) S)
    rw [hns, hinv]

end Alg

section Reduced
variable {R : Type} [CommRing R]

theorem eq_of_forall_field [IsReduced R] (a b : R)
    (h : ∀ (F : Type) [Field F] (χ : R →+* F), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  haveI := hJ
  letI : Field (FractionRing (R ⧸ J)) := inferInstance
  have hχ := h (FractionRing (R ⧸ J)) ((algebraMap (R ⧸ J) (FractionRing (R ⧸ J))).comp (Ideal.Quotient.mk J))
  rw [RingHom.comp_apply, RingHom.comp_apply] at hχ
  have hinj := IsFractionRing.injective (R ⧸ J) (FractionRing (R ⧸ J))
  have := hinj hχ
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

theorem isUnit_of_forall_field (a : R)
    (h : ∀ (F : Type) [Field F] (χ : R →+* F), χ a ≠ 0) : IsUnit a := by
  by_contra ha
  obtain ⟨M, hM, haM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr ha)
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  exact h (R ⧸ M) (Ideal.Quotient.mk M) (Ideal.Quotient.eq_zero_iff_mem.mpr haM)

end Reduced

section FieldCase
variable {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem xmul_field [W.IsElliptic] {m : ℤ} {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀) {x₁ y₁ : F}
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (hm : m • WeierstrassCurve.Affine.Point.some x₀ y₀ h₀ = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) :
    (W.ΨSq m).eval x₀ ≠ 0 ∧ x₁ * (W.ΨSq m).eval x₀ = (W.Φ m).eval x₀ := by
  have key := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq W m h₀ h₁ hm
  rw [WeierstrassCurve.Affine.evalEval_psi_sq W h₀.left m, WeierstrassCurve.Affine.evalEval_phi W h₀.left m] at key
  refine ⟨fun h0 => ?_, key⟩
  have hΦ : (W.Φ m).eval x₀ = 0 := by rw [← key, h0, mul_zero]
  obtain ⟨u, v, huv⟩ := WeierstrassCurve.isCoprime_Phi_PsiSq W m
  have := congrArg (Polynomial.eval x₀) huv
  rw [eval_add, eval_mul, eval_mul, hΦ, h0, mul_zero, mul_zero, add_zero, eval_one] at this
  exact zero_ne_one this

end FieldCase

end LinkRing

namespace LinkRing

theorem hom_eval_ΨSq {R S : Type*} [CommRing R] [CommRing S] (χ : R →+* S) (V : WeierstrassCurve R) (m : ℤ) (x : R) :
    χ ((V.ΨSq m).eval x) = ((V.map χ).ΨSq m).eval (χ x) := by
  rw [WeierstrassCurve.map_ΨSq, Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem hom_eval_Φ {R S : Type*} [CommRing R] [CommRing S] (χ : R →+* S) (V : WeierstrassCurve R) (m : ℤ) (x : R) :
    χ ((V.Φ m).eval x) = ((V.map χ).Φ m).eval (χ x) := by
  rw [WeierstrassCurve.map_Φ, Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem hom_eval_preΨ {R S : Type*} [CommRing R] [CommRing S] (χ : R →+* S) (V : WeierstrassCurve R) (m : ℤ) (x : R) :
    χ ((V.preΨ m).eval x) = ((V.map χ).preΨ m).eval (χ x) := by
  rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply]

section Univ
open ModularCurve.LevelP

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)

abbrev U : Type := UnivBase ℓ
abbrev PU : Type := UnivOnePoint ℓ
abbrev Wu : WeierstrassCurve (PU ℓ) := torsionPtCurve (univCurve ℓ) ℓ
abbrev tX : PU ℓ := torsionPtX (univCurve ℓ) ℓ
abbrev tY : PU ℓ := torsionPtY (univCurve ℓ) ℓ
abbrev Du : ModularCurve.LevelPData (PU ℓ) := ⟨tX ℓ, tY ℓ, tX ℓ, tY ℓ⟩

omit hℓ3 in
theorem hDu : ModularCurve.IsGamma1Point (Wu ℓ) ℓ (Du ℓ) :=
  ⟨equation_torsionPt _ _, preΨ_torsionPt _ _, rfl, rfl⟩

omit hℓ3 in
theorem hΔu : IsUnit (Wu ℓ).Δ := by
  rw [show (Wu ℓ) = (univCurve ℓ).map (TorsionPointRing.ofBase (univCurve ℓ) ℓ) from rfl, WeierstrassCurve.map_Δ]
  exact (isUnit_Δ_univCurve ℓ).map _

include hℓ3 in
theorem isReduced_PU : IsReduced (PU ℓ) := by
  have hp : ℓ.Prime := Fact.out
  haveI : IsDomain (U ℓ) := (ModularCurve.LevelP.isDomain_and_isIntegrallyClosed_univBase ℓ hp.ne_zero).1
  exact ModularCurve.LevelP.TorsionPointRing.isReduced_of_isUnit (univCurve ℓ) (hp.odd_of_ne_two (by omega)) (by omega)
    (isUnit_natCast_mul_Δ_univCurve ℓ)

theorem rep : ∃ (𝒢 : GroupLaws (U ℓ)) (𝒯 : LevelTransport (U ℓ) 𝒢 ℓ),
    𝒢.IsChordTangent ∧ 𝒢.IsOriginIdentity ∧ 𝒯.IsSectionTransport ∧
    (∀ (T : Type) [CommRing T] [Algebra (U ℓ) T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ) ∧
    (∀ (T T' : Type) [CommRing T] [Algebra (U ℓ) T] [CommRing T'] [Algebra (U ℓ) T'] (f : T →ₐ[U ℓ] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :=
  WeierstrassCurve.DrinfeldGlobal.exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport (U ℓ) ℓ

def 𝒢U : GroupLaws (U ℓ) := (rep ℓ).choose
omit hℓ3 in
theorem h𝒢U : (𝒢U ℓ).IsChordTangent := (rep ℓ).choose_spec.choose_spec.1
omit hℓ3 in
theorem h𝒢UO : (𝒢U ℓ).IsOriginIdentity := (rep ℓ).choose_spec.choose_spec.2.1

def diamEx := ModularCurve.LevelRelabelling.exists_natural_zsmul_gamma1Point (U ℓ) ℓ hℓ3 (isUnit_natCast_univBase ℓ)
  (𝒢U ℓ) (h𝒢U ℓ) (h𝒢UO ℓ)

def diamU := (diamEx ℓ hℓ3).choose

def Xu (m : ℤ) : PU ℓ := (diamU ℓ hℓ3 (PU ℓ) (Wu ℓ) m (Du ℓ)).xP

include hℓ3 in

theorem xmul_univ (m : ℤ) (hm : ¬ ((ℓ : ℤ) ∣ m)) :
    IsUnit (((Wu ℓ).ΨSq m).eval (tX ℓ)) ∧ Xu ℓ hℓ3 m * ((Wu ℓ).ΨSq m).eval (tX ℓ) = ((Wu ℓ).Φ m).eval (tX ℓ) := by
  haveI := isReduced_PU ℓ hℓ3

  have key : ∀ (F : Type) [Field F] (χ : PU ℓ →+* F),
      χ (((Wu ℓ).ΨSq m).eval (tX ℓ)) ≠ 0 ∧
        χ (Xu ℓ hℓ3 m * ((Wu ℓ).ΨSq m).eval (tX ℓ)) = χ (((Wu ℓ).Φ m).eval (tX ℓ)) := by
    intro F _ χ
    letI : Algebra (U ℓ) F := (χ.comp (algebraMap (U ℓ) (PU ℓ))).toAlgebra
    let χₐ : PU ℓ →ₐ[U ℓ] F := { toRingHom := χ, commutes' := fun r => rfl }
    have hχ : χₐ.toRingHom = χ := rfl
    have spec := (diamEx ℓ hℓ3).choose_spec

    have h3 := spec.2.2.1 (PU ℓ) F χₐ (Wu ℓ) (hΔu ℓ) m hm (Du ℓ) (hDu ℓ)
    rw [hχ] at h3
    change diamU ℓ hℓ3 F ((Wu ℓ).map χ) m ((Du ℓ).map χ) = (diamU ℓ hℓ3 (PU ℓ) (Wu ℓ) m (Du ℓ)).map χ at h3

    have hΔF : IsUnit ((Wu ℓ).map χ).Δ := by rw [WeierstrassCurve.map_Δ]; exact (hΔu ℓ).map χ
    have hDF : ModularCurve.IsGamma1Point ((Wu ℓ).map χ) ℓ ((Du ℓ).map χ) := (hDu ℓ).map χ
    have h2 := spec.2.1 F ((Wu ℓ).map χ) hΔF m hm ((Du ℓ).map χ) hDF
    have h1 := spec.1 F ((Wu ℓ).map χ) hΔF m hm ((Du ℓ).map χ) hDF
    haveI : ((Wu ℓ).map χ).IsElliptic := ⟨hΔF⟩
    have hΔ0 : ((Wu ℓ).map χ).Δ ≠ 0 := hΔF.ne_zero
    have nP : ((Wu ℓ).map χ).toAffine.Nonsingular (χ (tX ℓ)) (χ (tY ℓ)) :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ0).mp hDF.equation_P
    have nQ : ((Wu ℓ).map χ).toAffine.Nonsingular (diamU ℓ hℓ3 F ((Wu ℓ).map χ) m ((Du ℓ).map χ)).xP
        (diamU ℓ hℓ3 F ((Wu ℓ).map χ) m ((Du ℓ).map χ)).yP :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ0).mp h2.equation_P
    change toPoint ((Wu ℓ).map χ) (diamU ℓ hℓ3 F ((Wu ℓ).map χ) m ((Du ℓ).map χ)).xP
        (diamU ℓ hℓ3 F ((Wu ℓ).map χ) m ((Du ℓ).map χ)).yP = m • toPoint ((Wu ℓ).map χ) (χ (tX ℓ)) (χ (tY ℓ)) at h1
    unfold toPoint at h1
    rw [dif_pos nQ, dif_pos nP] at h1
    obtain ⟨hne, hid⟩ := xmul_field ((Wu ℓ).map χ) nP nQ h1.symm
    have hxP : (diamU ℓ hℓ3 F ((Wu ℓ).map χ) m ((Du ℓ).map χ)).xP = χ (Xu ℓ hℓ3 m) := by
      rw [h3]; rfl
    rw [← hom_eval_ΨSq] at hne hid
    rw [← hom_eval_Φ, hxP, ← map_mul] at hid
    exact ⟨hne, hid⟩
  exact ⟨isUnit_of_forall_field _ (fun F _ χ => (key F χ).1), eq_of_forall_field _ _ (fun F _ χ => (key F χ).2)⟩

include hℓ3 in

theorem xmul_ring {T : Type} [CommRing T] (hℓT : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ) (x₀ y₀ : T) (he : W.toAffine.Equation x₀ y₀)
    (hx : (W.preΨ ℓ).eval x₀ = 0) (m : ℤ) (hm : ¬ ((ℓ : ℤ) ∣ m)) :
    IsUnit ((W.ΨSq m).eval x₀) ∧
    ∀ (G : RelativeGroupLaw T (projModelStrCR W)) (hG : (G.one (𝟙 _)).1 = (kwZeroSect T W).1)
      (S : Section W) (hS : IsSectionThrough S x₀ y₀) (x₁ y₁ : T) (h₁ : IsSectionThrough (zsmulSection G m S) x₁ y₁),
      x₁ * (W.ΨSq m).eval x₀ = (W.Φ m).eval x₀ := by
  have hW : IsUnit (((ℓ : ℕ) : T) * W.Δ) := hℓT.mul hΔ
  let φ : U ℓ →+* T := UnivBase.lift ℓ W hW
  have hφ : (univCurve ℓ).map φ = W := univCurve_map_lift ℓ W hW
  obtain ⟨ψ, hψ0, hψx, hψy⟩ := ModularCurve.LevelP.TorsionPointRing.exists_ringHom_apply_torsionPt_eq (univCurve ℓ) ℓ φ x₀ y₀
    (by rw [hφ]; exact he) (by rw [hφ]; exact hx)
  have hWψ : (Wu ℓ).map ψ = W := by
    rw [show (Wu ℓ) = (univCurve ℓ).map (TorsionPointRing.ofBase (univCurve ℓ) ℓ) from rfl, WeierstrassCurve.map_map, hψ0, hφ]
  have hDψ : (Du ℓ).map ψ = (⟨x₀, y₀, x₀, y₀⟩ : ModularCurve.LevelPData T) := by
    ext <;> simp [hψx, hψy]
  obtain ⟨hunit, hid⟩ := xmul_univ ℓ hℓ3 m hm
  have hΨ : (W.ΨSq m).eval x₀ = ψ (((Wu ℓ).ΨSq m).eval (tX ℓ)) := by rw [hom_eval_ΨSq, hWψ, hψx]
  have hΦ : (W.Φ m).eval x₀ = ψ (((Wu ℓ).Φ m).eval (tX ℓ)) := by rw [hom_eval_Φ, hWψ, hψx]
  refine ⟨by rw [hΨ]; exact hunit.map ψ, ?_⟩
  intro G hG S hS x₁ y₁ h₁

  letI : Algebra (U ℓ) T := φ.toAlgebra
  have hcomm : ∀ r : U ℓ, ψ (algebraMap (U ℓ) (PU ℓ) r) = algebraMap (U ℓ) T r := by
    intro r
    show ψ (algebraMap (U ℓ) (PU ℓ) r) = φ r
    rw [ModularCurve.LevelP.TorsionPointRing.algebraMap_eq, ← RingHom.comp_apply, hψ0]
  let ψₐ : PU ℓ →ₐ[U ℓ] T := { toRingHom := ψ, commutes' := hcomm }
  have hψₐ : ψₐ.toRingHom = ψ := rfl
  have spec := (diamEx ℓ hℓ3).choose_spec
  haveI : W.toAffine.IsElliptic := ⟨hΔ⟩

  have e0 := (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢U ℓ T W hΔ)).mp
    (h𝒢UO ℓ T W hΔ)
  rw [zsmulSection_eq_of_one_eq G (𝒢U ℓ T W hΔ) (hG.trans e0.symm) m S] at h₁

  have hD₀ : ModularCurve.IsGamma1Point (W : WeierstrassCurve T) ℓ ⟨x₀, y₀, x₀, y₀⟩ := ⟨he, hx, rfl, rfl⟩
  have h7 := spec.2.2.2.2.2.2.2 T W hΔ m hm ⟨x₀, y₀, x₀, y₀⟩ hD₀ S hS
  obtain ⟨ex, -⟩ := ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).2
    _ _ _ _ _ _ h₁ h7).mp rfl

  have h3 := spec.2.2.1 (PU ℓ) T ψₐ (Wu ℓ) (hΔu ℓ) m hm (Du ℓ) (hDu ℓ)
  rw [hψₐ] at h3
  change diamU ℓ hℓ3 T ((Wu ℓ).map ψ) m ((Du ℓ).map ψ) = (diamU ℓ hℓ3 (PU ℓ) (Wu ℓ) m (Du ℓ)).map ψ at h3
  rw [hWψ, hDψ] at h3
  have hx₁ : x₁ = ψ (Xu ℓ hℓ3 m) := by
    rw [ex]
    change (diamU ℓ hℓ3 T W m ⟨x₀, y₀, x₀, y₀⟩).xP = _
    rw [h3]; rfl
  rw [hx₁, hΨ, hΦ, ← map_mul, hid]

end Univ

end LinkRing

namespace LinkRing

def fold (ℓ r : ℕ) : ℕ := if r ≤ (ℓ - 1) / 2 then r else ℓ - r

theorem fold_mem {ℓ r : ℕ} (hℓ : Odd ℓ) (hr : r < ℓ) (hr0 : r ≠ 0) : fold ℓ r ∈ Finset.Icc 1 ((ℓ - 1) / 2) := by
  unfold fold
  obtain ⟨k, rfl⟩ := hℓ
  have hk : (2 * k + 1 - 1) / 2 = k := by omega
  rw [hk, Finset.mem_Icc]
  split_ifs with h
  · omega
  · omega

theorem fold_cast {ℓ r : ℕ} (hr : r < ℓ) :
    ((fold ℓ r : ℕ) : ZMod ℓ) = (r : ZMod ℓ) ∨ ((fold ℓ r : ℕ) : ZMod ℓ) = -(r : ZMod ℓ) := by
  unfold fold
  split_ifs with h
  · exact Or.inl rfl
  · right
    rw [Nat.cast_sub hr.le, ZMod.natCast_self, zero_sub]

section PM
variable {R : Type} [Ring R]

theorem pm_symm {u v : R} (h : u = v ∨ u = -v) : v = u ∨ v = -u := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (neg_neg v).symm

theorem pm_trans {u v w : R} (h1 : u = v ∨ u = -v) (h2 : v = w ∨ v = -w) : u = w ∨ u = -w := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg w)

end PM

theorem pm_cancel {F : Type} [Field F] {a u v : F} (ha : a ≠ 0) (h : a * u = a * v ∨ a * u = -(a * v)) :
    u = v ∨ u = -v := by
  rcases h with h | h
  · exact Or.inl (mul_left_cancel₀ ha h)
  · rw [← mul_neg] at h
    exact Or.inr (mul_left_cancel₀ ha h)

end LinkRing

end

p2m_open "AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve ModularCurve.LevelRelabelling Polynomial AlgebraicGeometry.Polynomial"

open LinkRing in
theorem solution
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (T : Type) [CommRing T] [Algebra A T] (hℓT : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S : Section W) (x y : T) (hS : IsSectionThrough S x y) (hx : (W.preΨ ℓ).eval x = 0)
    (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
    (x' y' : T) (hS' : IsSectionThrough (ModularCurve.LevelRelabelling.zsmulSection (𝒢 T W hΔ) a S) x' y')
    (n : ℕ) :
    ∃ u : T, IsUnit u ∧ ModularCurve.inLineMulPoly W ℓ n x' = Polynomial.C u * ModularCurve.inLineMulPoly W ℓ n x := by
  classical
  have hp : ℓ.Prime := Fact.out
  have hℓ3 : 3 ≤ ℓ := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · have := hp.two_le; obtain ⟨k, hk⟩ := h; omega
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ2
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  haveI : (W : WeierstrassCurve T).toAffine.IsElliptic := ⟨hΔ⟩
  set G := 𝒢 T W hΔ with hGdef
  have hG : (G.one (𝟙 _)).1 = (kwZeroSect T W).1 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W G).mp (h𝒢O T W hΔ)

  have he : W.toAffine.Equation x y :=
    ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x y).mpr ⟨S, hS⟩
  have he' : W.toAffine.Equation x' y' :=
    ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x' y').mpr ⟨_, hS'⟩
  have hStors : G.nsmul (𝟙 _) ℓ S = G.one (𝟙 _) :=
    (WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough 𝒢 h𝒢 h𝒢O ℓ hℓ2 T hℓT W hΔ
      S x y hS).mpr hx
  have hx' : (W.preΨ ℓ).eval x' = 0 :=
    (WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough 𝒢 h𝒢 h𝒢O ℓ hℓ2 T hℓT W hΔ
      _ x' y' hS').mp (nsmul_zsmulSection_eq_one G S ℓ hStors a)

  set I : Finset ℕ := Finset.Icc 1 ((ℓ - 1) / 2) with hI
  set A : ZMod ℓ := ((a : ℤ) : ZMod ℓ) with hA
  have hA0 : A ≠ 0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a ℓ).mp h)
  let r : ℕ → ℕ := fun b => (A * (b : ZMod ℓ)).val
  let σ : ℕ → ℕ := fun b => fold ℓ (r b)
  have hr_lt : ∀ b, r b < ℓ := fun b => ZMod.val_lt _
  have hr_cast : ∀ b, ((r b : ℕ) : ZMod ℓ) = A * (b : ZMod ℓ) := fun b => ZMod.natCast_zmod_val _
  have hmemI : ∀ b ∈ I, 1 ≤ b ∧ b ≤ (ℓ - 1) / 2 := fun b hb => Finset.mem_Icc.mp hb
  have hl2 : 2 * ((ℓ - 1) / 2) < ℓ := by obtain ⟨k, hk⟩ := hodd; omega
  have hb0 : ∀ b ∈ I, (b : ZMod ℓ) ≠ 0 := by
    intro b hb h
    obtain ⟨h1, h2⟩ := hmemI b hb
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hndvdI : ∀ b ∈ I, ¬ ((ℓ : ℤ) ∣ (b : ℤ)) := by
    intro b hb h
    apply hb0 b hb
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (b : ℤ) ℓ).mpr h
    rwa [Int.cast_natCast] at this
  have hr0 : ∀ b ∈ I, r b ≠ 0 := by
    intro b hb h0
    have : A * (b : ZMod ℓ) = 0 := by rw [← hr_cast b, h0, Nat.cast_zero]
    rcases mul_eq_zero.mp this with h | h
    · exact hA0 h
    · exact hb0 b hb h
  have hσmem : ∀ b ∈ I, σ b ∈ I := fun b hb => fold_mem hodd (hr_lt b) (hr0 b hb)
  have hσcast : ∀ b, ((σ b : ℕ) : ZMod ℓ) = A * (b : ZMod ℓ) ∨ ((σ b : ℕ) : ZMod ℓ) = -(A * (b : ZMod ℓ)) := by
    intro b
    rcases fold_cast (ℓ := ℓ) (hr_lt b) with h | h
    · left; rw [show σ b = fold ℓ (r b) from rfl, h, hr_cast]
    · right; rw [show σ b = fold ℓ (r b) from rfl, h, hr_cast]
  have hsmall : ∀ b₁ ∈ I, ∀ b₂ ∈ I, ((b₁ : ZMod ℓ) = (b₂ : ZMod ℓ) ∨ (b₁ : ZMod ℓ) = -(b₂ : ZMod ℓ)) → b₁ = b₂ := by
    intro b₁ hb₁ b₂ hb₂ h
    obtain ⟨h11, h12⟩ := hmemI b₁ hb₁
    obtain ⟨h21, h22⟩ := hmemI b₂ hb₂
    rcases h with h | h
    · have : (((b₁ : ℤ) - (b₂ : ℤ) : ℤ) : ZMod ℓ) = 0 := by push_cast; rw [h, sub_self]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      have habs := Int.eq_zero_of_abs_lt_dvd this (by rw [abs_lt]; constructor <;> omega)
      omega
    · have : (((b₁ : ℤ) + (b₂ : ℤ) : ℤ) : ZMod ℓ) = 0 := by push_cast; rw [h, neg_add_cancel]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      have habs := Int.eq_zero_of_abs_lt_dvd this (by rw [abs_lt]; constructor <;> omega)
      omega
  have hinj : Set.InjOn σ (I : Set ℕ) := by
    intro b₁ hb₁ b₂ hb₂ hσ
    have hb₁' : b₁ ∈ I := hb₁
    have hb₂' : b₂ ∈ I := hb₂
    apply hsmall b₁ hb₁' b₂ hb₂'
    apply pm_cancel hA0
    have e : ((σ b₁ : ℕ) : ZMod ℓ) = ((σ b₂ : ℕ) : ZMod ℓ) := by rw [hσ]
    have h1 := pm_symm (hσcast b₁)
    rw [e] at h1
    exact pm_trans h1 (hσcast b₂)
  have hsurj : Set.SurjOn σ (I : Set ℕ) (I : Set ℕ) :=
    Finset.surjOn_of_injOn_of_card_le σ (fun b hb => hσmem b hb) hinj le_rfl

  let F : T → ℕ → T[X] := fun x₀ m => W.Φ n * C ((W.ΨSq m).eval x₀) - C ((W.Φ m).eval x₀) * W.ΨSq n
  have hprod : ∀ x₀ : T, ModularCurve.inLineMulPoly W ℓ n x₀ = ∏ b ∈ I, F x₀ b := fun x₀ => rfl

  have hfac : ∀ b ∈ I, ∃ c : T, IsUnit c ∧ F x' b = C c * F x (σ b) := by
    intro b hb
    have hb' := hσmem b hb
    obtain ⟨hb1, hb2⟩ := hmemI b hb
    have hbℤ : ¬ ((ℓ : ℤ) ∣ (b : ℤ)) := hndvdI b hb

    obtain ⟨mb, hmb_cast, hmb_abs⟩ : ∃ mb : ℤ, ((mb : ℤ) : ZMod ℓ) = A * (b : ZMod ℓ) ∧ (mb = (σ b : ℤ) ∨ mb = -(σ b : ℤ)) := by
      rcases hσcast b with h | h
      · exact ⟨(σ b : ℤ), by rw [Int.cast_natCast, h], Or.inl rfl⟩
      · exact ⟨-(σ b : ℤ), by rw [Int.cast_neg, Int.cast_natCast, h, neg_neg], Or.inr rfl⟩
    have hmbℤ : ¬ ((ℓ : ℤ) ∣ mb) := by
      intro h
      rcases hmb_abs with e | e
      · exact hndvdI _ hb' (by rwa [e] at h)
      · exact hndvdI _ hb' (by rw [e] at h; exact (dvd_neg.mp h))

    have hℓT' := hℓT
    obtain ⟨xb, yb, hSb⟩ := WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero 𝒢 h𝒢 h𝒢O
      ℓ hℓ3 T hℓT W hΔ (zsmulSection G a S) x' y' hS' hx' b hbℤ
    have eab : zsmulSection G b (zsmulSection G a S) = zsmulSection G mb S := by
      rw [zsmulSection_zsmulSection]
      exact zsmulSection_eq_of_nsmul_eq_one G S ℓ hStors (a * b) mb (by rw [hmb_cast, hA]; push_cast; ring)

    obtain ⟨uΨ', hid'⟩ := xmul_ring ℓ hℓ3 hℓT W hΔ x' y' he' hx' b hbℤ
    have hxb' : xb * (W.ΨSq b).eval x' = (W.Φ b).eval x' := hid' G hG _ hS' xb yb hSb
    obtain ⟨uΨm, hidm⟩ := xmul_ring ℓ hℓ3 hℓT W hΔ x y he hx mb hmbℤ
    have hxbm : xb * (W.ΨSq mb).eval x = (W.Φ mb).eval x := hidm G hG S hS xb yb (by rw [← eab]; exact hSb)

    have eΨ : W.ΨSq mb = W.ΨSq (σ b : ℕ) := by
      rcases hmb_abs with e | e
      · rw [e]
      · rw [e, WeierstrassCurve.ΨSq_neg]
    have eΦ : W.Φ mb = W.Φ (σ b : ℕ) := by
      rcases hmb_abs with e | e
      · rw [e]
      · rw [e, WeierstrassCurve.Φ_neg]
    rw [eΨ] at hxbm uΨm
    rw [eΦ] at hxbm

    have hcross : (W.Φ (b : ℕ)).eval x' * (W.ΨSq (σ b : ℕ)).eval x = (W.Φ (σ b : ℕ)).eval x * (W.ΨSq (b : ℕ)).eval x' := by
      rw [← hxb', ← hxbm]; ring
    obtain ⟨c, hc⟩ : ∃ c : T, c = (W.ΨSq (b : ℕ)).eval x' * ↑(uΨm.unit⁻¹) := ⟨_, rfl⟩
    have hu1 : (↑(uΨm.unit⁻¹) : T) * (W.ΨSq (σ b : ℕ)).eval x = 1 := uΨm.val_inv_mul
    have hc1 : c * (W.ΨSq (σ b : ℕ)).eval x = (W.ΨSq (b : ℕ)).eval x' := by
      rw [hc, mul_assoc, hu1, mul_one]
    have hc2 : c * (W.Φ (σ b : ℕ)).eval x = (W.Φ (b : ℕ)).eval x' := by
      have : c * (W.Φ (σ b : ℕ)).eval x * (W.ΨSq (σ b : ℕ)).eval x = (W.Φ (b : ℕ)).eval x' * (W.ΨSq (σ b : ℕ)).eval x := by
        rw [hcross, hc]; linear_combination ((W.ΨSq (b : ℕ)).eval x' * (W.Φ (σ b : ℕ)).eval x) * hu1
      exact (uΨm.mul_left_inj).mp this
    refine ⟨c, (by rw [hc]; exact uΨ'.mul (Units.isUnit _)), ?_⟩
    show W.Φ n * C ((W.ΨSq (b : ℕ)).eval x') - C ((W.Φ (b : ℕ)).eval x') * W.ΨSq n =
      C c * (W.Φ n * C ((W.ΨSq (σ b : ℕ)).eval x) - C ((W.Φ (σ b : ℕ)).eval x) * W.ΨSq n)
    rw [← hc1, ← hc2, C_mul, C_mul]
    ring

  choose c hcu hcF using hfac
  refine ⟨∏ b ∈ I.attach, c b.1 b.2, ?_, ?_⟩
  · exact Finset.prod_induction _ (fun t => IsUnit t) (fun _ _ h1 h2 => h1.mul h2) isUnit_one (fun b _ => hcu b.1 b.2)
  · rw [hprod, hprod, ← Finset.prod_attach I (f := F x')]
    rw [Finset.prod_congr rfl (fun (b : {b // b ∈ I}) (_ : b ∈ I.attach) => hcF b.1 b.2), Finset.prod_mul_distrib,
      ← map_prod C]
    congr 1
    rw [Finset.prod_attach I (f := fun b => F x (σ b))]
    exact Finset.prod_nbij σ hσmem hinj hsurj (fun b hb => rfl)

end S_WeierstrassCurve_DrinfeldGlobal_exists_isUnit_inLineMulPoly_eq_C_mul_of_isSectionThrough_zsmulSection
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isUnit_inLineMulPoly_eq_C_mul_of_isSectionThrough_zsmulSection (solution)
