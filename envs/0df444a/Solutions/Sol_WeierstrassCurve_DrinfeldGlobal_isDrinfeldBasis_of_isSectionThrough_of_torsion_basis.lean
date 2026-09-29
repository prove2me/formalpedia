-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isSectionThrough_of_torsion_basis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/76e098d8-4aa6-5b55-a52e-857ddd1666f7

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj
import Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isSectionThrough_of_torsion_basis
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve.LevelRelabelling
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P1cAux

variable {T : Type} [Field T]

local notation "tT" => Spec.map (CommRingCat.ofHom (algebraMap T T))

lemma tT_eq : (tT : base (T := T) ⟶ base (T := T)) = 𝟙 _ := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

lemma hψ : 𝟙 (base (T := T)) ≫ 𝟙 (base (T := T)) = tT := by
  rw [Category.id_comp, tT_eq]

variable (W : WeierstrassCurve.Projective T)

def τ (S : Section W) : NeronModelInfra.SchemeHomOver tT (projModelStrCR W) :=
  schemeHomOverComp (𝟙 _) hψ S

lemma τ_val (S : Section W) : (τ W S).1 = S.1 := by
  show 𝟙 _ ≫ S.1 = S.1
  exact Category.id_comp _

lemma τ_injective : Function.Injective (τ W) := by
  intro S₁ S₂ h
  apply Subtype.ext
  rw [← τ_val W S₁, ← τ_val W S₂, h]

variable (G : RelativeGroupLaw T (projModelStrCR W))

lemma τ_mul (X Y : Section W) : τ W (G.mul (𝟙 _) X Y) = G.mul tT (τ W X) (τ W Y) :=
  G.mul_natural _ _ _ hψ X Y

lemma τ_nsmul (n : ℕ) (X : Section W) : τ W (G.nsmul (𝟙 _) n X) = G.nsmul tT n (τ W X) :=
  G.nsmul_natural _ _ _ hψ n X

lemma τ_one : τ W (G.one (𝟙 _)) = G.one tT :=
  G.one_natural _ _ _ hψ

lemma bc_eq : W.baseChange T = W := by
  show W.map (algebraMap T T) = W
  rw [Algebra.algebraMap_self]
  exact W.map_id

def ptCast {W₁ W₂ : WeierstrassCurve T} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

lemma ptCast_some {W₁ W₂ : WeierstrassCurve T} (e : W₁ = W₂) (x y : T) (h : W₁.toAffine.Nonsingular x y) :
    ∃ h' : W₂.toAffine.Nonsingular x y, ptCast e (.some x y h) = .some x y h' := by
  subst e; exact ⟨h, rfl⟩

variable (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
    NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W) ≃
      (W.baseChange F).toAffine.Point)

def Φ (S : Section W) : W.toAffine.Point := ptCast (bc_eq W) (ev T (τ W S))

lemma Φ_injective : Function.Injective (Φ W ev) := fun _ _ h =>
  τ_injective W ((ev T).injective ((ptCast (bc_eq W)).injective h))

lemma Φ_mul (hev : IsPointsEval W G ev) (X Y : Section W) :
    Φ W ev (G.mul (𝟙 _) X Y) = Φ W ev X + Φ W ev Y := by
  unfold Φ
  rw [τ_mul, hev.1, map_add]

lemma Φ_one (hG1 : (G.one (𝟙 _)).1 = (kwZeroSect T W).1)
    (hev0 : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
      ev F ⟨Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (kwZeroSect T W).1,
        by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ = 0) :
    Φ W ev (G.one (𝟙 _)) = 0 := by
  unfold Φ
  have h1 : G.one tT = ⟨tT ≫ (kwZeroSect T W).1,
      by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ := by
    rw [← τ_one W G]
    apply Subtype.ext
    show 𝟙 _ ≫ (G.one (𝟙 _)).1 = tT ≫ (kwZeroSect T W).1
    rw [hG1, tT_eq]
  rw [τ_one, h1, hev0 T, map_zero]

lemma Φ_nsmul (hev : IsPointsEval W G ev) (hG1 : (G.one (𝟙 _)).1 = (kwZeroSect T W).1)
    (hev0 : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
      ev F ⟨Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (kwZeroSect T W).1,
        by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ = 0)
    (n : ℕ) (X : Section W) :
    Φ W ev (G.nsmul (𝟙 _) n X) = n • Φ W ev X := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, Φ_one W G ev hG1 hev0, zero_nsmul]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, Φ_mul W G ev hev, ih, add_nsmul, one_nsmul]

lemma Φ_through
    (hevc : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F]
      (P : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W))
      (χ : ZChartRing W →+* F),
      P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W →
      ∃ hxy : (W.baseChange F).toAffine.Nonsingular (χ (xOverZ W)) (χ (yOverZ W)),
        ev F P = WeierstrassCurve.Affine.Point.some _ _ hxy)
    (S : Section W) (χ : ZChartRing W →+* T) (hS : IsZChartSection S χ) :
    Φ W ev S = toPoint W (affX χ) (affY χ) := by
  obtain ⟨hxy, h⟩ := hevc T (τ W S) χ (by rw [τ_val]; exact hS)
  unfold Φ
  rw [h]
  obtain ⟨h', e'⟩ := ptCast_some (bc_eq W) (χ (xOverZ W)) (χ (yOverZ W)) hxy
  rw [e']
  show _ = toPoint W (χ (xOverZ W)) (χ (yOverZ W))
  rw [toPoint, dif_pos h']

lemma inj_of_torsion {M : Type} [AddCommGroup M] (q : ℕ) (hq : 0 < q) (p p' : M)
    (hP : (q : ℤ) • p = 0) (hP' : (q : ℤ) • p' = 0)
    (hind : ∀ a b : ℕ, a < q → b < q → (a : ℤ) • p + (b : ℤ) • p' = 0 → a = 0 ∧ b = 0)
    (a b a' b' : ℕ) (ha : a < q) (hb : b < q) (ha' : a' < q) (hb' : b' < q)
    (h : a • p + b • p' = a' • p + b' • p') : a = a' ∧ b = b' := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hqne : (q : ℤ) ≠ 0 := ne_of_gt hq'

  have key : ∀ (n : ℤ) (m : M), (q : ℤ) • m = 0 → (((n % q).toNat : ℕ) : ℤ) • m = n • m := by
    intro n m hm
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hqne), Int.emod_def, sub_zsmul, mul_zsmul', hm]
    simp
  have h0 : ((a : ℤ) - a') • p + ((b : ℤ) - b') • p' = 0 := by
    have h' : (a • p + b • p') - (a' • p + b' • p') = 0 := sub_eq_zero.mpr h
    rw [sub_zsmul, sub_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul, ← h']
    abel
  set c : ℕ := (((a : ℤ) - a') % q).toNat with hc
  set d : ℕ := (((b : ℤ) - b') % q).toNat with hd
  have hcq : c < q := by
    rw [hc, Int.toNat_lt (Int.emod_nonneg _ hqne)]
    exact Int.emod_lt_of_pos _ hq'
  have hdq : d < q := by
    rw [hd, Int.toNat_lt (Int.emod_nonneg _ hqne)]
    exact Int.emod_lt_of_pos _ hq'
  have hcd := hind c d hcq hdq (by rw [hc, hd, key _ _ hP, key _ _ hP', h0])

  have aux : ∀ (u v : ℕ), u < q → v < q → (((u : ℤ) - v) % q).toNat = 0 → u = v := by
    intro u v hu hv h0
    have hle : ((u : ℤ) - v) % q ≤ 0 := Int.toNat_eq_zero.mp h0
    have hz : ((u : ℤ) - v) % q = 0 := le_antisymm hle (Int.emod_nonneg _ hqne)
    have hdvd : (q : ℤ) ∣ (u : ℤ) - v := Int.dvd_of_emod_eq_zero hz
    have hmod : (v : ℤ) % q = (u : ℤ) % q := Int.modEq_iff_dvd.mpr hdvd
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hv),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hu)] at hmod
    exact_mod_cast hmod.symm
  exact ⟨aux a a' ha ha' (hc ▸ hcd.1), aux b b' hb hb' (hd ▸ hcd.2)⟩

end P1cAux

theorem solution
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    {T : Type} [Field T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (q : ℕ) (hq : ((q : ℕ) : T) ≠ 0)
    (S S' : Section W) (x y x' y' : T)
    (hS : IsSectionThrough S x y) (hS' : IsSectionThrough S' x' y')
    (hP : (q : ℤ) • toPoint W x y = 0) (hP' : (q : ℤ) • toPoint W x' y' = 0)
    (hind : ∀ a b : ℕ, a < q → b < q →
      (a : ℤ) • toPoint W x y + (b : ℤ) • toPoint W x' y' = 0 → a = 0 ∧ b = 0) :
    IsDrinfeldBasis (𝒢 T W hΔ) q S S' := by
  classical
  haveI : WeierstrassCurve.IsElliptic W := ⟨hΔ⟩
  have hG1 : ((𝒢 T W hΔ).one (𝟙 _)).1 = (kwZeroSect T W).1 :=
    (RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢 T W hΔ)).mp (h𝒢O T W hΔ)
  obtain ⟨ev, hev, hev0, hevc⟩ :=
    exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain W (𝒢 T W hΔ) hG1
  obtain ⟨χ, hχ, rfl, rfl⟩ := hS
  obtain ⟨χ', hχ', rfl, rfl⟩ := hS'
  have eS : P1cAux.Φ W ev S = toPoint W (affX χ) (affY χ) := P1cAux.Φ_through W ev hevc S χ hχ
  have eS' : P1cAux.Φ W ev S' = toPoint W (affX χ') (affY χ') := P1cAux.Φ_through W ev hevc S' χ' hχ'
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact hq (by simp))
  refine isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj W hΔ (𝒢 T W hΔ) ev hev q hq S S' ?_ ?_ ?_
  · apply P1cAux.Φ_injective W ev
    rw [P1cAux.Φ_nsmul W _ ev hev hG1 hev0, P1cAux.Φ_one W _ ev hG1 hev0, eS, ← natCast_zsmul]
    exact hP
  · apply P1cAux.Φ_injective W ev
    rw [P1cAux.Φ_nsmul W _ ev hev hG1 hev0, P1cAux.Φ_one W _ ev hG1 hev0, eS', ← natCast_zsmul]
    exact hP'
  · intro a b a' b' ha hb ha' hb' h
    have h2 := congrArg (P1cAux.Φ W ev) h
    simp only [linComb, P1cAux.Φ_mul W _ ev hev, P1cAux.Φ_nsmul W _ ev hev hG1 hev0, eS, eS'] at h2
    exact P1cAux.inj_of_torsion q hq0 _ _ hP hP' hind a b a' b' ha hb ha' hb' h2

end
end S_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isSectionThrough_of_torsion_basis
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isSectionThrough_of_torsion_basis (solution)
