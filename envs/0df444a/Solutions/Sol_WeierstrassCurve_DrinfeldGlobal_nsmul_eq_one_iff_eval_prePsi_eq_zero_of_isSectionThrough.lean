-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3c01c325-8891-5398-a659-0db0fa4b13ed

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_exists_relativeGroupLaw_one_eq_zeroSect_isPointsEval_of_isUnit
import Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq
import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_isReduced_schemeKer_of_isPointsEval_of_isUnit
import Theorems.Thm_ModularCurve_LevelP_TorsionPointRing_isReduced_of_isUnit
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq"
p2m_attr_erase "simp" "NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace KTRing

theorem genericCurve_Δ_ne_zero : (LevelP.genericCurve).Δ ≠ 0 := by
  intro h

  have h2 := congrArg (MvPolynomial.eval (fun i : Fin 5 => if i = 4 then (1 : ℤ) else 0)) h
  rw [← WeierstrassCurve.map_Δ, map_zero] at h2
  revert h2
  simp [LevelP.genericCurve, WeierstrassCurve.map, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem pDelta_ne_zero (ℓ : ℕ) (hℓ : ℓ ≠ 0) : LevelP.pDelta ℓ ≠ 0 := by
  rw [LevelP.pDelta]
  exact mul_ne_zero (by exact_mod_cast hℓ) genericCurve_Δ_ne_zero

scoped instance isDomain_univBase (ℓ : ℕ) [Fact ℓ.Prime] : IsDomain (LevelP.UnivBase ℓ) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (LevelP.pDelta ℓ)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (pDelta_ne_zero ℓ (Fact.out : ℓ.Prime).ne_zero))

scoped instance isNoetherianRing_univBase (ℓ : ℕ) : IsNoetherianRing (LevelP.UnivBase ℓ) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (LevelP.pDelta ℓ)) _ inferInstance

theorem exists_classifyingMap (ℓ : ℕ) {T : Type} [CommRing T] (W : WeierstrassCurve T)
    (hℓT : IsUnit ((ℓ : ℕ) : T)) (hΔ : IsUnit W.Δ) :
    ∃ f : LevelP.UnivBase ℓ →+* T, (LevelP.univCurve ℓ).map f = W := by
  set g : MvPolynomial (Fin 5) ℤ →+* T := MvPolynomial.eval₂Hom (Int.castRingHom T) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
    with hg
  have hgW : LevelP.genericCurve.map g = W := by
    simp [LevelP.genericCurve, WeierstrassCurve.map, hg]
  have hunit : IsUnit (g (LevelP.pDelta ℓ)) := by
    rw [LevelP.pDelta, map_mul, map_natCast, ← WeierstrassCurve.map_Δ, hgW]
    exact hℓT.mul hΔ
  refine ⟨IsLocalization.Away.lift (LevelP.pDelta ℓ) hunit, ?_⟩
  rw [LevelP.univCurve, WeierstrassCurve.map_map, IsLocalization.Away.lift_comp, hgW]

section GroupLaw

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem val_nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  conv_lhs => rw [← hx]
  rw [← G.nsmul_natural f t x.1 x.2 n]
  rfl

theorem val_one (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  rw [← G.one_natural (𝟙 _) t t (Category.comp_id _)]
  rfl

theorem nsmul_eq_one_iff (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t n x = G.one t ↔ x.1 ≫ G.schemeNsmul n = t ≫ (G.one (𝟙 _)).1 := by
  rw [← val_nsmul, ← val_one]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end GroupLaw

section Eval

universe u

variable {K : Type u} [CommRing K] (V : WeierstrassCurve.Projective K)
  (G : RelativeGroupLaw K (projModelStrCR V))
  (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra K F],
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR V) ≃
      (V.baseChange F).toAffine.Point)

theorem ev_one (hev : IsPointsEval V G ev) (F : Type u) [Field F] [DecidableEq F] [Algebra K F] :
    ev F (G.one _) = 0 := by
  have h := hev.1 F (G.one _) (G.one _)
  rw [G.one_mul] at h
  have h' : ev F (G.one _) + ev F (G.one _) = ev F (G.one _) + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h'

theorem ev_nsmul (hev : IsPointsEval V G ev) (F : Type u) [Field F] [DecidableEq F] [Algebra K F]
    (n : ℕ) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR V)) :
    ev F (G.nsmul _ n x) = n • ev F x := by
  induction n with
  | zero => rw [G.nsmul_zero, ev_one V G ev hev, zero_smul]
  | succ n ih => rw [G.nsmul_succ, hev.1, ih, succ_nsmul]

end Eval

section Chart

universe u

variable {B : Type u} [CommRing B] (V : WeierstrassCurve.Projective B)

abbrev CR : Type u := Polynomial (Polynomial B) ⧸ Ideal.span {V.toAffine.polynomial}

noncomputable abbrev mkCR : Polynomial (Polynomial B) →+* CR V :=
  Ideal.Quotient.mk (Ideal.span {V.toAffine.polynomial})

noncomputable abbrev toChart : B →+* ZChartRing V :=
  (fromZeroRingHom (projModelGradingCR V) (Submonoid.powers (coord V 2))).comp
    (algebraMap B (projModelGradingCR V 0))

theorem exists_equiv :
    ∃ f : ZChartRing V →+* CR V, Function.Bijective f ∧
      (∀ t : B, f (toChart V t) = mkCR V (Polynomial.C (Polynomial.C t))) ∧
      f (xOverZ V) = mkCR V (Polynomial.C Polynomial.X) ∧
      f (yOverZ V) = mkCR V Polynomial.X := by
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V
  refine ⟨f, hbij, ?_, ?_, ?_⟩
  · intro t
    exact RingHom.congr_fun hcomp t
  · have hb : (X 0 : MvPolynomial (Fin 3) B) ∈ MvPolynomial.homogeneousSubmodule (Fin 3) B (1 • 1) := by
      simpa using (MvPolynomial.isHomogeneous_X B (0 : Fin 3))
    have := hmk 1 (X 0) hb
    (first | exact this | simpa [xOverZ] using this | (have h__ := this; simp [xOverZ] at h__; exact h__))
  · have hb : (X 1 : MvPolynomial (Fin 3) B) ∈ MvPolynomial.homogeneousSubmodule (Fin 3) B (1 • 1) := by
      simpa using (MvPolynomial.isHomogeneous_X B (1 : Fin 3))
    have := hmk 1 (X 1) hb
    (first | exact this | simpa [yOverZ] using this | (have h__ := this; simp [yOverZ] at h__; exact h__))

theorem specMap_comp_zChartι_comp_str {T : Type u} [CommRing T] (χ : ZChartRing V →+* T) :
    (Spec.map (CommRingCat.ofHom χ) ≫ zChartι V) ≫ projModelStrCR V =
      Spec.map (CommRingCat.ofHom (χ.comp (toChart V))) := by
  rw [projModelStrCR, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem comp_toChart_eq_of_over {T : Type u} [CommRing T] (χ : ZChartRing V →+* T) (φ : B →+* T)
    (h : (Spec.map (CommRingCat.ofHom χ) ≫ zChartι V) ≫ projModelStrCR V = Spec.map (CommRingCat.ofHom φ)) :
    χ.comp (toChart V) = φ := by
  rw [specMap_comp_zChartι_comp_str] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem ringHom_CR_ext {T : Type u} [CommRing T] {g g' : CR V →+* T}
    (hC : ∀ t : B, g (mkCR V (Polynomial.C (Polynomial.C t))) = g' (mkCR V (Polynomial.C (Polynomial.C t))))
    (hx : g (mkCR V (Polynomial.C Polynomial.X)) = g' (mkCR V (Polynomial.C Polynomial.X)))
    (hy : g (mkCR V Polynomial.X) = g' (mkCR V Polynomial.X)) : g = g' := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · exact RingHom.ext fun t => hC t
    · exact hx
  · exact hy

theorem chart_ext {T : Type u} [CommRing T] {χ χ' : ZChartRing V →+* T}
    (hb : χ.comp (toChart V) = χ'.comp (toChart V)) (hx : χ (xOverZ V) = χ' (xOverZ V))
    (hy : χ (yOverZ V) = χ' (yOverZ V)) : χ = χ' := by
  obtain ⟨f, hbij, hcomp, hfx, hfy⟩ := exists_equiv V
  set e : ZChartRing V ≃+* CR V := RingEquiv.ofBijective f hbij with he
  have key : χ.comp e.symm.toRingHom = χ'.comp e.symm.toRingHom := by
    apply ringHom_CR_ext
    · intro t
      have : e.symm (mkCR V (Polynomial.C (Polynomial.C t))) = toChart V t := by
        apply e.injective; rw [RingEquiv.apply_symm_apply]; exact (hcomp t).symm
      show χ (e.symm _) = χ' (e.symm _)
      rw [this]; exact RingHom.congr_fun hb t
    · have : e.symm (mkCR V (Polynomial.C Polynomial.X)) = xOverZ V := by
        apply e.injective; rw [RingEquiv.apply_symm_apply]; exact hfx.symm
      show χ (e.symm _) = χ' (e.symm _)
      rw [this]; exact hx
    · have : e.symm (mkCR V Polynomial.X) = yOverZ V := by
        apply e.injective; rw [RingEquiv.apply_symm_apply]; exact hfy.symm
      show χ (e.symm _) = χ' (e.symm _)
      rw [this]; exact hy
  ext a
  have := congrArg (fun φ : CR V →+* T => φ (e a)) key
  simpa using this

noncomputable def evR {T : Type u} [CommRing T] (φ : B →+* T) {x y : T}
    (hxy : (V.map φ).toAffine.Equation x y) : CR V →+* T :=
  Ideal.Quotient.lift _ ((Polynomial.evalEvalRingHom x y).comp (Polynomial.mapRingHom (Polynomial.mapRingHom φ))) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul]
    have : ((Polynomial.evalEvalRingHom x y).comp (Polynomial.mapRingHom (Polynomial.mapRingHom φ)))
        V.toAffine.polynomial = 0 := by
      show Polynomial.evalEval x y (V.toAffine.polynomial.map (Polynomial.mapRingHom φ)) = 0
      rw [← WeierstrassCurve.Affine.map_polynomial]
      exact hxy
    rw [this, zero_mul])

theorem evR_mk {T : Type u} [CommRing T] (φ : B →+* T) {x y : T} (hxy : (V.map φ).toAffine.Equation x y)
    (p : Polynomial (Polynomial B)) :
    evR V φ hxy (mkCR V p) = Polynomial.evalEval x y (p.map (Polynomial.mapRingHom φ)) := by
  rw [evR, Ideal.Quotient.lift_mk]
  rfl

theorem exists_chart {T : Type u} [CommRing T] (φ : B →+* T) {x y : T}
    (hxy : (V.map φ).toAffine.Equation x y) :
    ∃ χ : ZChartRing V →+* T, χ.comp (toChart V) = φ ∧ χ (xOverZ V) = x ∧ χ (yOverZ V) = y := by
  obtain ⟨f, hbij, hcomp, hfx, hfy⟩ := exists_equiv V
  refine ⟨(evR V φ hxy).comp f, ?_, ?_, ?_⟩
  · ext t
    show evR V φ hxy (f (toChart V t)) = φ t
    rw [hcomp, evR_mk, Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.evalEval_C,
      Polynomial.eval_C]
  · show evR V φ hxy (f (xOverZ V)) = x
    rw [hfx, evR_mk, Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.evalEval_C,
      Polynomial.eval_X]
  · show evR V φ hxy (f (yOverZ V)) = y
    rw [hfy, evR_mk, Polynomial.map_X, Polynomial.evalEval_X]

theorem equation_chart {T : Type u} [CommRing T] (χ : ZChartRing V →+* T) :
    (V.map (χ.comp (toChart V))).toAffine.Equation (χ (xOverZ V)) (χ (yOverZ V)) := by
  obtain ⟨f, hbij, hcomp, hfx, hfy⟩ := exists_equiv V
  set e : ZChartRing V ≃+* CR V := RingEquiv.ofBijective f hbij with he
  have s1 : ∀ t : B, e.symm (mkCR V (Polynomial.C (Polynomial.C t))) = toChart V t := by
    intro t; apply e.injective; rw [RingEquiv.apply_symm_apply]; exact (hcomp t).symm
  have s2 : e.symm (mkCR V (Polynomial.C Polynomial.X)) = xOverZ V := by
    apply e.injective; rw [RingEquiv.apply_symm_apply]; exact hfx.symm
  have s3 : e.symm (mkCR V Polynomial.X) = yOverZ V := by
    apply e.injective; rw [RingEquiv.apply_symm_apply]; exact hfy.symm
  have hg : (χ.comp e.symm.toRingHom).comp (mkCR V) =
      (Polynomial.evalEvalRingHom (χ (xOverZ V)) (χ (yOverZ V))).comp
        (Polynomial.mapRingHom (Polynomial.mapRingHom (χ.comp (toChart V)))) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · refine RingHom.ext fun t => ?_
        show χ (e.symm (mkCR V (Polynomial.C (Polynomial.C t)))) = _
        rw [s1]; simp
      · show χ (e.symm (mkCR V (Polynomial.C Polynomial.X))) = _
        rw [s2]; simp
    · show χ (e.symm (mkCR V Polynomial.X)) = _
      rw [s3]; simp
  have h0 : (χ.comp e.symm.toRingHom) (mkCR V V.toAffine.polynomial) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
  have := congrArg (fun φ : Polynomial (Polynomial B) →+* T => φ V.toAffine.polynomial) hg
  simp only [RingHom.coe_comp, Function.comp_apply] at this h0
  have h3 : Polynomial.evalEval (χ (xOverZ V)) (χ (yOverZ V))
      ((Polynomial.mapRingHom (Polynomial.mapRingHom (χ.comp (toChart V)))) V.toAffine.polynomial) =
      χ (e.symm.toRingHom (mkCR V V.toAffine.polynomial)) := this.symm
  rw [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.map_polynomial]
  exact h3.trans h0

end Chart

theorem schemeHomOver_eq_of_forall_field {B T : Type} [CommRing B] [CommRing T] [IsReduced T]
    (V : WeierstrassCurve.Projective B) [V.toAffine.IsElliptic] (f : B →+* T)
    (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR V))
    (h : ∀ (F : Type) [Field F] (g : T →+* F),
      Spec.map (CommRingCat.ofHom g) ≫ P.1 = Spec.map (CommRingCat.ofHom g) ≫ Q.1) :
    P = Q := by
  have hprop := WeierstrassProjModel.projModelStrCR_isProper V
  haveI : IsSeparated (projModelStrCR V) := inferInstance
  apply Subtype.ext
  refine ext_of_fromSpecResidueField_eq P.1 Q.1 (projModelStrCR V) Set.univ dense_univ ?_ (P.2.trans Q.2.symm)
  intro t _
  have key := h _ (((Spec (CommRingCat.of T)).residue t).hom.comp (StructureSheaf.toStalk T t).hom)
  simp only [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc] at key
  rw [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq', Category.assoc, Category.assoc]
  exact key

theorem nsmul_eq_one_iff_field {B : Type} [CommRing B] [IsDomain B] [IsNoetherianRing B] (V : WeierstrassCurve B)
    [V.IsElliptic] (G : RelativeGroupLaw B (projModelStrCR V.toProjective))
    (hG : (G.one (𝟙 _)).1 = (kwZeroSect B V).1) {n : ℕ} (hn : Odd n)
    (F : Type) [Field F] [DecidableEq F] [Algebra B F] (hΔF : IsUnit (V.map (algebraMap B F)).Δ)
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B F))) (projModelStrCR V.toProjective))
    (χ : ZChartRing V.toProjective →+* F) (hP : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι V.toProjective) :
    G.nsmul _ n P = G.one _ ↔ ((V.map (algebraMap B F)).preΨ n).eval (χ (xOverZ V.toProjective)) = 0 := by
  obtain ⟨ev, hev, -, hevc⟩ :=
    WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain V G hG
  obtain ⟨hxy, hevP⟩ := hevc F P χ hP
  haveI : (V.toProjective.baseChange F).IsElliptic := ⟨by simpa [WeierstrassCurve.baseChange] using hΔF⟩
  have h1 : G.nsmul _ n P = G.one _ ↔ n • ev F P = 0 := by
    rw [← ev_nsmul V.toProjective G ev hev, ← ev_one V.toProjective G ev hev F]
    exact ⟨fun h => by rw [h], fun h => (ev F).injective h⟩
  rw [h1, hevP, WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi _ hn hxy,
    WeierstrassCurve.preΨ_ofNat]
  rfl

theorem odd_of_prime_ne_two {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) : Odd ℓ :=
  (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2

theorem nsmul_eq_one_of_eval_preΨ_eq_zero_univ {B T : Type} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [CommRing T] (V : WeierstrassCurve B) [hV : V.IsElliptic] (f : B →+* T)
    (G : RelativeGroupLaw B (projModelStrCR V.toProjective)) (hG : (G.one (𝟙 _)).1 = (kwZeroSect B V).1)
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra B F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B F))) (projModelStrCR V.toProjective) ≃
        (V.toProjective.baseChange F).toAffine.Point)
    (hev : IsPointsEval V.toProjective G ev)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓB : IsUnit ((ℓ : ℕ) : B))
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR V.toProjective))
    (χ : ZChartRing V.toProjective →+* T) (hP : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι V.toProjective)
    (hψ : ((V.map f).preΨ ℓ).eval (χ (xOverZ V.toProjective)) = 0) :
    G.nsmul _ ℓ P = G.one _ := by
  classical
  have hℓodd : Odd ℓ := odd_of_prime_ne_two hℓ2
  have hℓ1 : ℓ ≠ 1 := (Fact.out : ℓ.Prime).one_lt.ne'

  have hχf : χ.comp (toChart V.toProjective) = f :=
    comp_toChart_eq_of_over V.toProjective χ f (by rw [← hP]; exact P.2)
  have hxy : (V.map f).toAffine.Equation (χ (xOverZ V.toProjective)) (χ (yOverZ V.toProjective)) := by
    have := equation_chart V.toProjective χ
    rwa [hχf] at this

  set PR := LevelP.TorsionPointRing V ℓ
  set φ₀ : B →+* PR := LevelP.TorsionPointRing.ofBase V ℓ with hφ₀
  haveI : IsReduced PR := ModularCurve.LevelP.TorsionPointRing.isReduced_of_isUnit V hℓodd hℓ1 (hℓB.mul hV.isUnit)
  obtain ⟨χ₀, hχ₀b, hχ₀x, hχ₀y⟩ := exists_chart V.toProjective φ₀ (x := LevelP.torsionPtX V ℓ)
    (y := LevelP.torsionPtY V ℓ) (LevelP.equation_torsionPt V ℓ)
  have hover₀ : (Spec.map (CommRingCat.ofHom χ₀) ≫ zChartι V.toProjective) ≫ projModelStrCR V.toProjective =
      Spec.map (CommRingCat.ofHom φ₀) := by
    rw [specMap_comp_zChartι_comp_str, hχ₀b]
  set P₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom φ₀)) (projModelStrCR V.toProjective) :=
    ⟨Spec.map (CommRingCat.ofHom χ₀) ≫ zChartι V.toProjective, hover₀⟩ with hP₀

  have htors₀ : P₀.1 ≫ G.schemeNsmul ℓ = Spec.map (CommRingCat.ofHom φ₀) ≫ (G.one (𝟙 _)).1 := by
    let Q₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom φ₀)) (projModelStrCR V.toProjective) :=
      ⟨P₀.1 ≫ G.schemeNsmul ℓ, by rw [Category.assoc, G.schemeNsmul_over]; exact P₀.2⟩
    let Q₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom φ₀)) (projModelStrCR V.toProjective) :=
      ⟨Spec.map (CommRingCat.ofHom φ₀) ≫ (G.one (𝟙 _)).1, by rw [Category.assoc, (G.one (𝟙 _)).2, Category.comp_id]⟩
    suffices hQ : Q₁ = Q₂ from congrArg Subtype.val hQ
    apply schemeHomOver_eq_of_forall_field V.toProjective φ₀ Q₁ Q₂
    intro F _ g
    letI : Algebra B F := (g.comp φ₀).toAlgebra
    have halg : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom φ₀) =
        Spec.map (CommRingCat.ofHom (algebraMap B F)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

    let PF : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B F))) (projModelStrCR V.toProjective) :=
      ⟨Spec.map (CommRingCat.ofHom g) ≫ P₀.1, by rw [Category.assoc, P₀.2, halg]⟩
    have hPF : PF.1 = Spec.map (CommRingCat.ofHom (g.comp χ₀)) ≫ zChartι V.toProjective := by
      show Spec.map (CommRingCat.ofHom g) ≫ (Spec.map (CommRingCat.ofHom χ₀) ≫ zChartι V.toProjective) = _
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hΔF : IsUnit (V.map (algebraMap B F)).Δ := by
      rw [WeierstrassCurve.map_Δ]; exact hV.isUnit.map _
    have hψF : ((V.map (algebraMap B F)).preΨ ℓ).eval ((g.comp χ₀) (xOverZ V.toProjective)) = 0 := by
      have e1 : algebraMap B F = g.comp φ₀ := rfl
      rw [e1, ← WeierstrassCurve.map_map, RingHom.comp_apply, hχ₀x, LevelP.preΨ_eval_map]
      show g (((LevelP.torsionPtCurve V ℓ).preΨ ℓ).eval (LevelP.torsionPtX V ℓ)) = 0
      rw [LevelP.preΨ_torsionPt, map_zero]
    have key := (nsmul_eq_one_iff_field V G hG hℓodd F hΔF PF (g.comp χ₀) hPF).mpr hψF
    rw [nsmul_eq_one_iff] at key

    have key2 : (Spec.map (CommRingCat.ofHom g) ≫ P₀.1) ≫ G.schemeNsmul ℓ =
        (Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom φ₀)) ≫ (G.one (𝟙 _)).1 := by
      rw [halg]; exact key
    show Spec.map (CommRingCat.ofHom g) ≫ (P₀.1 ≫ G.schemeNsmul ℓ) =
      Spec.map (CommRingCat.ofHom g) ≫ (Spec.map (CommRingCat.ofHom φ₀) ≫ (G.one (𝟙 _)).1)
    rw [← Category.assoc, key2, Category.assoc]

  obtain ⟨ψ, hψb, hψx, hψy⟩ := LevelP.TorsionPointRing.exists_ringHom_apply_torsionPt_eq V ℓ f
    (χ (xOverZ V.toProjective)) (χ (yOverZ V.toProjective)) hxy hψ
  have hχψ : χ = ψ.comp χ₀ := by
    apply chart_ext V.toProjective
    · rw [hχf, RingHom.comp_assoc, hχ₀b]; exact hψb.symm
    · rw [RingHom.comp_apply, hχ₀x, hψx]
    · rw [RingHom.comp_apply, hχ₀y, hψy]
  have hP' : P.1 = Spec.map (CommRingCat.ofHom ψ) ≫ P₀.1 := by
    rw [hP, hχψ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [nsmul_eq_one_iff, hP', Category.assoc, htors₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψb]

theorem eval_preΨ_eq_zero_of_nsmul_eq_one_univ {B T : Type} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [CommRing T] (V : WeierstrassCurve B) [hV : V.IsElliptic] (f : B →+* T)
    (G : RelativeGroupLaw B (projModelStrCR V.toProjective)) (hG : (G.one (𝟙 _)).1 = (kwZeroSect B V).1)
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra B F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B F))) (projModelStrCR V.toProjective) ≃
        (V.toProjective.baseChange F).toAffine.Point)
    (hev : IsPointsEval V.toProjective G ev)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓB : IsUnit ((ℓ : ℕ) : B))
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR V.toProjective))
    (χ : ZChartRing V.toProjective →+* T) (hP : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι V.toProjective)
    (hℓP : G.nsmul _ ℓ P = G.one _) :
    ((V.map f).preΨ ℓ).eval (χ (xOverZ V.toProjective)) = 0 := by
  classical
  have hℓodd : Odd ℓ := odd_of_prime_ne_two hℓ2
  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos

  have hχf : χ.comp (toChart V.toProjective) = f :=
    comp_toChart_eq_of_over V.toProjective χ f (by rw [← hP]; exact P.2)

  haveI : IsReduced (G.schemeKer ℓ) :=
    WeierstrassProjModel.RelativeGroupLaw.isReduced_schemeKer_of_isPointsEval_of_isUnit V.toProjective G ev hev hℓB hℓpos
  have hk : pullback.fst (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 ≫ G.schemeNsmul ℓ =
      pullback.snd (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 ≫ (G.one (𝟙 _)).1 := pullback.condition
  have hkstr : pullback.fst (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 ≫ projModelStrCR V.toProjective =
      pullback.snd (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 := by
    calc pullback.fst (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 ≫ projModelStrCR V.toProjective
        = pullback.fst (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 ≫ G.schemeNsmul ℓ ≫ projModelStrCR V.toProjective := by
          rw [G.schemeNsmul_over]
      _ = (pullback.snd (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 ≫ (G.one (𝟙 _)).1) ≫ projModelStrCR V.toProjective := by
          rw [← Category.assoc, hk]
      _ = pullback.snd (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 := by
          rw [Category.assoc, (G.one (𝟙 _)).2, Category.comp_id]
  let U : Scheme := pullback (pullback.fst (G.schemeNsmul ℓ) (G.one (𝟙 _)).1) (zChartι V.toProjective)
  let u₁ : U ⟶ G.schemeKer ℓ := pullback.fst _ _
  let u₂ : U ⟶ Spec (CommRingCat.of (ZChartRing V.toProjective)) := pullback.snd _ _
  haveI : IsReduced U := isReduced_of_isOpenImmersion u₁
  have hu : u₁ ≫ pullback.fst (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 = u₂ ≫ zChartι V.toProjective :=
    pullback.condition

  let ψ : ZChartRing V.toProjective :=
    ((V.map (toChart V.toProjective)).preΨ ℓ).eval (xOverZ V.toProjective)
  let ψD : Γ(Spec (CommRingCat.of (ZChartRing V.toProjective)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (ZChartRing V.toProjective))).inv ψ

  have hvan : ∀ u : U, ψ ∈ (u₂ u).asIdeal := by
    intro u
    let F : Type := U.residueField u
    set g := Spec.preimage (U.fromSpecResidueField u ≫ u₂) with hgdef
    have hg : Spec.map g = U.fromSpecResidueField u ≫ u₂ := Spec.map_preimage _

    obtain ⟨p₀⟩ : Nonempty (Spec (U.residueField u)) := ⟨IsLocalRing.closedPoint _⟩
    have hu₂u : u₂ u = Spec.map g p₀ := by
      rw [hg, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    suffices hgψ : g.hom ψ = 0 by
      rw [hu₂u, Spec.map_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hgψ]
      exact Ideal.zero_mem _

    letI : Algebra B F := (g.hom.comp (toChart V.toProjective)).toAlgebra
    have halg : algebraMap B F = g.hom.comp (toChart V.toProjective) := rfl
    have hover : (Spec.map g ≫ zChartι V.toProjective) ≫ projModelStrCR V.toProjective =
        Spec.map (CommRingCat.ofHom (algebraMap B F)) := by
      rw [halg, ← specMap_comp_zChartι_comp_str, CommRingCat.ofHom_hom]
    let PF : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B F))) (projModelStrCR V.toProjective) :=
      ⟨Spec.map g ≫ zChartι V.toProjective, hover⟩
    have hPF : PF.1 = Spec.map (CommRingCat.ofHom g.hom) ≫ zChartι V.toProjective := by
      rw [CommRingCat.ofHom_hom]
    have hΔF : IsUnit (V.map (algebraMap B F)).Δ := by
      rw [WeierstrassCurve.map_Δ]; exact hV.isUnit.map _

    have hPF1 : PF.1 = U.fromSpecResidueField u ≫ u₁ ≫ pullback.fst (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 := by
      show Spec.map g ≫ zChartι V.toProjective = _
      rw [hg, Category.assoc, hu]
    have htors : G.nsmul _ ℓ PF = G.one _ := by
      rw [nsmul_eq_one_iff]
      have e1 : Spec.map (CommRingCat.ofHom (algebraMap B F)) =
          U.fromSpecResidueField u ≫ u₁ ≫ pullback.snd (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 := by
        rw [← hover, show Spec.map g ≫ zChartι V.toProjective = PF.1 from rfl, hPF1]
        simp only [Category.assoc]
        rw [hkstr]
      calc PF.1 ≫ G.schemeNsmul ℓ
          = (U.fromSpecResidueField u ≫ u₁ ≫ pullback.fst (G.schemeNsmul ℓ) (G.one (𝟙 _)).1) ≫ G.schemeNsmul ℓ := by
            rw [hPF1]
        _ = (U.fromSpecResidueField u ≫ u₁ ≫ pullback.snd (G.schemeNsmul ℓ) (G.one (𝟙 _)).1) ≫ (G.one (𝟙 _)).1 := by
            simp only [Category.assoc]; rw [hk]
        _ = Spec.map (CommRingCat.ofHom (algebraMap B F)) ≫ (G.one (𝟙 _)).1 := by rw [← e1]
    have key := (nsmul_eq_one_iff_field V G hG hℓodd F hΔF PF g.hom hPF).mp htors
    rw [halg, ← WeierstrassCurve.map_map, LevelP.preΨ_eval_map] at key
    exact key

  have hs0 : u₂.appTop ψD = 0 := by
    rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    ext u
    constructor
    · intro hu'
      exact absurd ((PrimeSpectrum.mem_basicOpen _ _).mp hu') (not_not.mpr (hvan u))
    · intro h; exact h.elim

  have hP' : P.1 ≫ G.schemeNsmul ℓ = Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 _)).1 :=
    (nsmul_eq_one_iff G _ ℓ P).mp hℓP
  let Pt : Spec (CommRingCat.of T) ⟶ G.schemeKer ℓ := pullback.lift P.1 (Spec.map (CommRingCat.ofHom f)) hP'
  have hPt₁ : Pt ≫ pullback.fst (G.schemeNsmul ℓ) (G.one (𝟙 _)).1 = P.1 := pullback.lift_fst _ _ _
  let Q : Spec (CommRingCat.of T) ⟶ U :=
    pullback.lift Pt (Spec.map (CommRingCat.ofHom χ)) (by rw [hPt₁, hP])
  have hQ₂ : Q ≫ u₂ = Spec.map (CommRingCat.ofHom χ) := pullback.lift_snd _ _ _
  have hχψ : χ ψ = 0 := by
    have h1 : (Spec.map (CommRingCat.ofHom χ)).appTop ψD =
        (Scheme.ΓSpecIso (CommRingCat.of T)).inv (χ ψ) := by
      show ((Scheme.ΓSpecIso (CommRingCat.of (ZChartRing V.toProjective))).inv ≫
        (Spec.map (CommRingCat.ofHom χ)).appTop) ψ = _
      rw [← Scheme.ΓSpecIso_inv_naturality]; rfl
    have h2 : (Spec.map (CommRingCat.ofHom χ)).appTop ψD = 0 := by
      rw [← hQ₂, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hs0, map_zero]
    rw [h1] at h2
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of T)).hom h2
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at h3
    exact h3

  have : ((V.map f).preΨ ℓ).eval (χ (xOverZ V.toProjective)) = χ ψ := by
    rw [← hχf, ← WeierstrassCurve.map_map, LevelP.preΨ_eval_map]
  rw [this, hχψ]

end KTRing
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough.KTRing"

open KTRing

theorem solution
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (T : Type) [CommRing T] [Algebra A T] (hℓT : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S : Section W) (x y : T) (hS : IsSectionThrough S x y) :
    (𝒢 T W hΔ).nsmul (𝟙 _) ℓ S = (𝒢 T W hΔ).one (𝟙 _) ↔ (W.preΨ ℓ).eval x = 0 := by
  classical

  obtain ⟨f, hf⟩ := exists_classifyingMap ℓ W hℓT hΔ
  subst hf
  haveI hVell : (LevelP.univCurve ℓ).IsElliptic := ⟨LevelP.isUnit_Δ_univCurve ℓ⟩

  obtain ⟨G, ev, hG1, hev⟩ :=
    WeierstrassProjModel.exists_relativeGroupLaw_one_eq_zeroSect_isPointsEval_of_isUnit (LevelP.univCurve ℓ).toProjective
      (LevelP.isUnit_Δ_univCurve ℓ)
  have hG : (G.one (𝟙 _)).1 = (kwZeroSect (LevelP.UnivBase ℓ) (LevelP.univCurve ℓ)).1 := by
    rw [hG1 (𝟙 _), Category.id_comp]

  have hL : ((𝒢 T ((LevelP.univCurve ℓ).map f) hΔ).one (𝟙 _)).1 = (kwZeroSect T ((LevelP.univCurve ℓ).map f)).1 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect ((LevelP.univCurve ℓ).map f)
      (𝒢 T ((LevelP.univCurve ℓ).map f) hΔ)).mp (h𝒢O T ((LevelP.univCurve ℓ).map f) hΔ)

  obtain ⟨Φ, hsq, hpb, hnsmul, hone, hthrough⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect
      (LevelP.univCurve ℓ) f G hG (𝒢 T ((LevelP.univCurve ℓ).map f) hΔ) hL
  obtain ⟨χ, hχ, hχx, hχy⟩ := (hthrough S x y).mp hS
  set P : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR (LevelP.univCurve ℓ).toProjective) :=
    ⟨S.1 ≫ Φ, by rw [Category.assoc, hsq, ← Category.assoc, S.2, Category.id_comp]⟩ with hPdef

  have hinj : ∀ S₁ S₂ : Section ((LevelP.univCurve ℓ).map f).toProjective, S₁.1 ≫ Φ = S₂.1 ≫ Φ → S₁ = S₂ := by
    intro S₁ S₂ h
    apply Subtype.ext
    exact hpb.hom_ext h (by rw [S₁.2, S₂.2])
  have key : (𝒢 T ((LevelP.univCurve ℓ).map f) hΔ).nsmul (𝟙 _) ℓ S = (𝒢 T ((LevelP.univCurve ℓ).map f) hΔ).one (𝟙 _) ↔
      G.nsmul (Spec.map (CommRingCat.ofHom f)) ℓ P = G.one (Spec.map (CommRingCat.ofHom f)) := by
    constructor
    · intro h
      apply Subtype.ext
      rw [← hone, ← hnsmul ℓ S, h]
    · intro h
      apply hinj
      rw [hnsmul ℓ S, hone]
      exact congrArg Subtype.val h
  rw [key, ← hχx]
  have hℓB : IsUnit ((ℓ : ℕ) : LevelP.UnivBase ℓ) := LevelP.isUnit_natCast_univBase ℓ
  constructor
  · intro h
    exact eval_preΨ_eq_zero_of_nsmul_eq_one_univ (LevelP.univCurve ℓ) f G hG ev hev ℓ hℓ2 hℓB P χ hχ h
  · intro h
    exact nsmul_eq_one_of_eval_preΨ_eq_zero_univ (LevelP.univCurve ℓ) f G hG ev hev ℓ hℓ2 hℓB P χ hχ h

end S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough (solution)
