-- Prove2me | solution 1 for WeierstrassProjModel.isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8be788ad-48c9-5ccc-a474-a7301481db9f

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo
import Theorems.Thm_WeierstrassProjModel_flat_schemeFibreEndo_schemeNsmul_of_isPointsEval_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry P2MW.S_WeierstrassProjModel_isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic.AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic.WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelStrCR IsPointsEval projModelStrCR_smoothOfRelativeDimension_one flat_schemeFibreEndo_schemeNsmul_of_isPointsEval_of_isElliptic isFinite_schemeKerStr_of_isPointsEval projModel_pullback_iso_baseChange"
namespace TorsionFLF
p2m_open "WeierstrassProjModel"

theorem exists_ne_zero_and_smul_eq_zero {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    [V.IsElliptic] (F : Type u) [Field F] [DecidableEq F] [Algebra R F] [IsAlgClosed F]
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hℓF : (ℓ : F) ≠ 0) :
    ∃ P : (V.baseChange F).toAffine.Point, P ≠ 0 ∧ ℓ • P = 0 := by
  haveI : (V.baseChange F).IsElliptic := inferInstanceAs ((V.map (algebraMap R F)).IsElliptic)
  obtain ⟨L, -, -, hcard, -⟩ :=
    WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq (Ω := F) (V.baseChange F) hℓF
  letI : Algebra R L := ((algebraMap F L).comp (algebraMap R F)).toAlgebra
  haveI : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have e : (V.baseChange F).baseChange L = V.baseChange L :=
    WeierstrassCurve.map_baseChange (W := V) (Algebra.ofId F L)
  have aux : ∀ {W₁ W₂ : WeierstrassCurve L}, W₁ = W₂ →
      Nat.card {P : W₁.toAffine.Point // ℓ • P = 0} = ℓ ^ 2 →
      Nat.card {P : W₂.toAffine.Point // ℓ • P = 0} = ℓ ^ 2 := by
    rintro _ _ rfl h; exact h
  replace hcard := aux e hcard
  set T := {P : (V.baseChange L).toAffine.Point // ℓ • P = 0} with hT
  have hcard1 : 1 < Nat.card T := by
    rw [hcard]
    exact Nat.one_lt_pow two_ne_zero (by omega)
  haveI : Finite T := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp hcard1
  obtain ⟨⟨P, hP⟩, hP0⟩ := exists_ne (⟨0, by simp⟩ : T)
  have hP0' : P ≠ 0 := fun h ↦ hP0 (Subtype.ext h)
  refine ⟨WeierstrassCurve.Affine.Point.map (IntermediateField.val L) P, ?_, ?_⟩
  · intro h
    apply hP0'
    apply WeierstrassCurve.Affine.Point.map_injective (f := IntermediateField.val L)
    rw [h, map_zero]
  · rw [← map_nsmul, hP, map_zero]

end WeierstrassProjModel.TorsionFLF

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "HasRingHomProperty.iff_of_isAffine IsZariskiLocalAtTarget.restrict SmoothOfRelativeDimension.smooth IsZariskiLocalAtSource.iff_of_iSup_eq_top morphismRestrict_comp SmoothOfRelativeDimension Scheme.Hom iSup_affineOpens_eq_top IsFinite IsAffine IsZariskiLocalAtTarget LocallyOfFiniteType Spec Spec.map Scheme Smooth IsZariskiLocalAtSource Scheme.Hom.comp_appTop Flat HasRingHomProperty.comp_of_isOpenImmersion morphismRestrict_ι_assoc IsZariskiLocalAtTarget.iff_of_iSup_eq_top LocallyOfFinitePresentation HasRingHomProperty flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo"
p2m_open "AlgebraicGeometry"

theorem locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (hg : LocallyOfFiniteType g)
    (h : LocallyOfFinitePresentation (f ≫ g)) : LocallyOfFinitePresentation f := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    exact this (IsZariskiLocalAtTarget.restrict hg U.1) H inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
      (f ⁻¹ᵁ U.1).ι (f ≫ g) h
    rw [← morphismRestrict_ι_assoc] at H
    refine this ?_ H inferInstance
    infer_instance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
      U.1.ι (f ≫ g) h
    rw [← Category.assoc] at H
    exact this H inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)] at hg
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact RingHom.FinitePresentation.of_comp_finiteType _ h hg

end AlgebraicGeometry

open WeierstrassProjModel.TorsionFLF in
theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) {n : ℕ} (hn : 0 < n) :
    IsFinite (G.schemeKerStr n) ∧ Flat (G.schemeKerStr n) ∧ LocallyOfFinitePresentation (G.schemeKerStr n) := by
  haveI hV : V.IsElliptic := ‹V.toAffine.IsElliptic›

  haveI : SmoothOfRelativeDimension 1 (projModelStrCR V) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one V
  haveI : Smooth (projModelStrCR V) := SmoothOfRelativeDimension.smooth 1 _
  haveI : Flat (projModelStrCR V) := inferInstance
  haveI : LocallyOfFinitePresentation (projModelStrCR V) := inferInstance

  haveI hflat : Flat (G.schemeNsmul n) :=
    AlgebraicGeometry.flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo
      (projModelStrCR V) (G.schemeNsmul n) (G.schemeNsmul_over n)
      (fun s ↦ WeierstrassProjModel.flat_schemeFibreEndo_schemeNsmul_of_isPointsEval_of_isElliptic
        V G ev hev n hn.ne' s)

  haveI hlfp : LocallyOfFinitePresentation (G.schemeNsmul n) :=
    AlgebraicGeometry.locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
      (g := projModelStrCR V) inferInstance (by rw [G.schemeNsmul_over n]; infer_instance)
  refine ⟨?_, inferInstance, inferInstance⟩

  exact WeierstrassProjModel.isFinite_schemeKerStr_of_isPointsEval V
    (WeierstrassProjModel.projModel_pullback_iso_baseChange V) G ev hev
    (fun F _ _ _ _ ℓ hℓ hℓF ↦ exists_ne_zero_and_smul_eq_zero V F ℓ hℓ.two_le hℓF) hn

end S_WeierstrassProjModel_isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic
end P2MW
export P2MW.S_WeierstrassProjModel_isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic (solution)
