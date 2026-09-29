-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.exists_moduleFinite_flat_represents_nsmul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/56109993-6aad-588c-97e8-b3174d0a41da

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Theorems.Thm_WeierstrassProjModel_isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_moduleFinite_flat_represents_nsmul_eq_one
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

namespace TorsRepAsm

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem one_val (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := G.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  rw [← h, schemeHomOverComp_coe]

theorem nsmul_val (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x := by
    apply Subtype.ext
    rw [schemeHomOverComp_coe]
    exact Category.comp_id _
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h, schemeHomOverComp_coe]
  rfl

theorem nsmul_eq_one_iff (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) :
    G.nsmul t n x = G.one t ↔ x.1 ≫ G.schemeNsmul n = t ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  rw [Subtype.ext_iff, nsmul_val, one_val]

end TorsRepAsm

open TorsRepAsm in
set_option maxHeartbeats 6400000 in

theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) (q : ℕ) (hq : 0 < q) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Module.Finite R C) (_ : Module.Flat R C)
      (Qu : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R C))) (projModelStrCR V))
      (_ : G.nsmul _ q Qu = G.one _),
      ∀ (T : Type u) [CommRing T] [Algebra R T]
        (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) (projModelStrCR V)),
        G.nsmul _ q Q = G.one _ ↔
          ∃! ψ : C →ₐ[R] T, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Qu.1 = Q.1 := by
  classical
  obtain ⟨hKfin, hKflat, -⟩ :=
    WeierstrassProjModel.isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic V G ev hev hq

  have hκstr : pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 ≫ projModelStrCR V = G.schemeKerStr q := by
    have h1 := pullback.condition (f := G.schemeNsmul q) (g := (G.one (𝟙 _)).1)
    have h2 := congrArg (· ≫ projModelStrCR V) h1
    simp only [Category.assoc, RelativeGroupLaw.schemeNsmul_over] at h2
    rw [h2, (G.one (𝟙 _)).2, Category.comp_id]
  haveI : IsClosedImmersion (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    have : IsClosedImmersion ((G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ projModelStrCR V) := by
      rw [(G.one (𝟙 _)).2]; infer_instance
    exact IsClosedImmersion.of_comp (g := projModelStrCR V) _
  haveI hκmono : Mono (pullback.fst (G.schemeNsmul q) (G.one (𝟙 (Spec (CommRingCat.of R)))).1) := by
    infer_instance

  haveI := hKfin
  haveI := hKflat
  let Y : Scheme.{u} := G.schemeKer q
  let t₀ : Y ⟶ Spec (CommRingCat.of R) := G.schemeKerStr q
  let κ : Y ⟶ projModelCR V := pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1
  haveI : IsFinite t₀ := hKfin
  haveI : Flat t₀ := hKflat
  haveI : IsAffine Y := isAffine_of_isAffineHom t₀

  let C : Type u := Γ(Y, ⊤)
  let φ₀ : R →+* C := (t₀.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  letI : Algebra R C := φ₀.toAlgebra
  have hfinC : Module.Finite R C := by
    have h1 : (t₀.appTop).hom.Finite := Scheme.Hom.finite_appTop _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
    have : φ₀.Finite := h1.comp h2
    exact this

  have hstr : Spec.map (CommRingCat.ofHom (algebraMap R C)) = Y.isoSpec.inv ≫ t₀ := by
    change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ t₀.appTop) = _
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]
  have hflatC : Module.Flat R C := by
    have h1 : Flat (Spec.map (CommRingCat.ofHom (algebraMap R C))) := by
      rw [hstr]; infer_instance
    have h2 : (algebraMap R C).Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp h1
    exact RingHom.flat_algebraMap_iff.mp h2

  let Qu : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R C))) (projModelStrCR V) :=
    ⟨Y.isoSpec.inv ≫ κ, by rw [Category.assoc, hκstr, hstr]⟩
  have hQu : G.nsmul _ q Qu = G.one _ := by
    rw [nsmul_eq_one_iff]
    change (Y.isoSpec.inv ≫ κ) ≫ G.schemeNsmul q = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (G.one (𝟙 _)).1
    rw [Category.assoc, pullback.condition, hstr, Category.assoc]

  have key : ∀ (T : Type u) [CommRing T] [Algebra R T] (v : Spec (CommRingCat.of T) ⟶ Y),
      v ≫ t₀ = Spec.map (CommRingCat.ofHom (algebraMap R T)) →
      ∃ ψ : C →ₐ[R] T, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.isoSpec.inv = v := by
    intro T _ _ v hv
    let ψ₀ : C →+* T := (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom.comp (v.appTop).hom
    have hψ₀ : Spec.map (CommRingCat.ofHom ψ₀) ≫ Y.isoSpec.inv = v := by
      change Spec.map (v.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) ≫ Y.isoSpec.inv = v
      rw [Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality, ← Scheme.isoSpec_Spec_hom,
        Iso.hom_inv_id_assoc]
    have hcomm : ∀ r : R, ψ₀ (algebraMap R C r) = algebraMap R T r := by
      intro r
      have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R T))
      have e2 : (Spec.map (CommRingCat.ofHom (algebraMap R T))).appTop = t₀.appTop ≫ v.appTop := by
        rw [← Scheme.Hom.comp_appTop, hv]
      have h3 := congrArg (fun g : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of T =>
        g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) nat
      rw [e2] at h3
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
      have h4 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r := by
        rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_apply]
      rw [h4] at h3
      exact h3
    exact ⟨⟨ψ₀, hcomm⟩, hψ₀⟩
  refine ⟨C, inferInstance, inferInstance, hfinC, hflatC, Qu, hQu, ?_⟩
  intro T _ _ Q
  constructor
  · intro hQ

    have hQ' : Q.1 ≫ G.schemeNsmul q = Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ (G.one (𝟙 _)).1 :=
      (nsmul_eq_one_iff G _ q Q).mp hQ
    let u : Spec (CommRingCat.of T) ⟶ Y := pullback.lift Q.1 (Spec.map (CommRingCat.ofHom (algebraMap R T))) hQ'
    have huκ : u ≫ κ = Q.1 := pullback.lift_fst _ _ _
    have hut : u ≫ t₀ = Spec.map (CommRingCat.ofHom (algebraMap R T)) := pullback.lift_snd _ _ _
    obtain ⟨ψ, hψ⟩ := key T u hut
    refine ⟨ψ, ?_, ?_⟩
    · change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (Y.isoSpec.inv ≫ κ) = Q.1
      rw [← Category.assoc, hψ, huκ]
    · intro ψ' hψ'
      have h1 : (Spec.map (CommRingCat.ofHom ψ'.toRingHom) ≫ Y.isoSpec.inv) ≫ κ = u ≫ κ := by
        rw [huκ, Category.assoc]; exact hψ'
      have h2 : Spec.map (CommRingCat.ofHom ψ'.toRingHom) ≫ Y.isoSpec.inv = u := (cancel_mono κ).mp h1
      rw [← hψ, cancel_mono] at h2
      have h3 := Spec.map_injective h2
      apply AlgHom.ext
      intro c
      exact congrArg (fun g : CommRingCat.of C ⟶ CommRingCat.of T => g.hom c) h3
  · rintro ⟨ψ, hψ, -⟩
    rw [nsmul_eq_one_iff]
    have hQ1 : Q.1 = (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.isoSpec.inv) ≫ κ := by
      rw [Category.assoc]; exact hψ.symm
    have ht : Spec.map (CommRingCat.ofHom (algebraMap R T)) =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.isoSpec.inv ≫ G.schemeKerStr q := by
      rw [← Q.2, hQ1]; simp only [Category.assoc]; rw [hκstr]
    rw [hQ1, ht]
    simp only [Category.assoc]
    rw [pullback.condition]

end S_WeierstrassProjModel_RelativeGroupLaw_exists_moduleFinite_flat_represents_nsmul_eq_one
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_moduleFinite_flat_represents_nsmul_eq_one (solution)
