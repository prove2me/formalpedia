-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/891f4408-6514-595a-a3ce-5db4a9990943

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_map_eq_smul_one_of_zlinComb_eq_zsmulSection
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "ModularCurve WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit.WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing"

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.unusedVariables false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra ModularCurve.LevelRelabelling HomogeneousLocalization

open scoped Classical

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map Affine.Point.some map_id toAffine Affine.Point Δ Projective baseChange"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "base Section IsDrinfeldBasis RawDrinfeldPair IsCoefficientHom coord ZChartRing zChartι IsZChartSection affX affY IsSectionThrough GroupLaws RawDrinfeldPair.IsLevel LevelTransport equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough IsDrinfeldBasis.map_eq_smul_one_of_zlinComb_eq_zsmulSection"
namespace DrinfeldThrough
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

section General

variable {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}

abbrev σT (T : Type) [CommRing T] : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of T) :=
  Spec.map (CommRingCat.ofHom (algebraMap T T))

theorem σT_eq_id (T : Type) [CommRing T] : σT T = 𝟙 (Spec (CommRingCat.of T)) := by
  show Spec.map (CommRingCat.ofHom (algebraMap T T)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

def bc (S : Section W) : SchemeHomOver (σT T) (projModelStrCR W) :=
  schemeHomOverComp (σT T) (Category.comp_id _) S

theorem bc_val (S : Section W) : (bc S).1 = S.1 := by
  show σT T ≫ S.1 = S.1
  rw [σT_eq_id, Category.id_comp]

theorem bc_injective {S S' : Section W} (h : bc S = bc S') : S = S' := by
  apply Subtype.ext
  rw [← bc_val S, ← bc_val S', h]

variable (G : RelativeGroupLaw T (projModelStrCR W))

theorem bc_mul (S S' : Section W) : bc (G.mul _ S S') = G.mul _ (bc S) (bc S') :=
  G.mul_natural _ _ _ _ S S'

theorem bc_one : bc (G.one (𝟙 _) : Section W) = G.one (σT T) :=
  G.one_natural _ _ _ _

variable {P : Type} [AddCommGroup P] (E : SchemeHomOver (σT T) (projModelStrCR W) ≃ P)
  (hE : ∀ p q, E (G.mul _ p q) = E p + E q)

include hE

theorem E_one : E (G.one (σT T)) = 0 := by
  have h : E (G.one (σT T)) + E (G.one (σT T)) = E (G.one (σT T)) + 0 := by
    rw [← hE, G.one_mul, add_zero]
  exact add_left_cancel h

theorem E_bc_one : E (bc (G.one (𝟙 _) : Section W)) = 0 := by
  rw [bc_one, E_one G E hE]

end General

section FieldCase

theorem ne_one_of_isDrinfeldBasis {K : Type} [Field K] (W : WeierstrassCurve.Projective K) (hΔ : IsUnit W.Δ)
    (G : RelativeGroupLaw K (projModelStrCR W))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR W) ≃ (W.baseChange F).toAffine.Point)
    (hev : IsPointsEval W G ev) (q : ℕ) [Fact q.Prime] (hqK : (q : K) ≠ 0) (P Q : Section W)
    (h : IsDrinfeldBasis G q P Q) :
    P ≠ G.one (𝟙 _) ∧ Q ≠ G.one (𝟙 _) := by
  refine ⟨fun hP1 => ?_, fun hQ1 => ?_⟩
  · have key := IsDrinfeldBasis.map_eq_smul_one_of_zlinComb_eq_zsmulSection W hΔ G ev hev q hqK P Q h
      !![0, 0; 0, 1] 1 (Or.inl rfl)
      (by
        show G.mul _ (G.nsmul _ 0 P) (G.nsmul _ 0 Q) = G.nsmul _ 1 P
        rw [hP1]; rfl)
      (by
        show G.mul _ (G.nsmul _ 0 P) (G.nsmul _ 1 Q) = G.nsmul _ 1 Q
        exact G.one_mul _ _)
    have h00 := congrFun (congrFun key 0) 0
    simp at h00
  · have key := IsDrinfeldBasis.map_eq_smul_one_of_zlinComb_eq_zsmulSection W hΔ G ev hev q hqK P Q h
      !![1, 0; 0, 0] 1 (Or.inl rfl)
      (by
        show G.mul _ (G.nsmul _ 1 P) (G.nsmul _ 0 Q) = G.nsmul _ 1 P
        exact G.mul_one _ _)
      (by
        show G.mul _ (G.nsmul _ 0 P) (G.nsmul _ 0 Q) = G.nsmul _ 1 Q
        rw [hQ1]; rfl)
    have h11 := congrFun (congrFun key 1) 1
    simp at h11

theorem exists_isSectionThrough_of_ne_one {A₀ : Type} [CommRing A₀] (𝒢 : GroupLaws A₀)
    (h𝒢O : 𝒢.IsOriginIdentity) {K : Type} [Field K] [Algebra A₀ K]
    (W : WeierstrassCurve.Projective K) (hΔ : IsUnit W.Δ) (R : Section W) (hR : R ≠ (𝒢 K W hΔ).one (𝟙 _)) :
    ∃ x y : K, IsSectionThrough R x y := by
  haveI : WeierstrassCurve.IsElliptic W := ⟨hΔ⟩
  obtain ⟨χ0, hχ0, hχ0x, hχ0z⟩ := h𝒢O K W hΔ
  have hG1 : ((𝒢 K W hΔ).one (𝟙 _)).1 = (kwZeroSect K W).1 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢 K W hΔ)).mp
      ⟨χ0, hχ0, hχ0x, hχ0z⟩
  obtain ⟨ev, hev, -, hevc⟩ :=
    WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain W (𝒢 K W hΔ) hG1
  let E : SchemeHomOver (σT K) (projModelStrCR W) ≃ W.toAffine.Point := ev K
  have hE : ∀ p p', E ((𝒢 K W hΔ).mul _ p p') = E p + E p' := fun p p' => hev.1 K p p'
  have hread : ∀ (S : Section W) (u v : K), IsSectionThrough S u v →
      ∃ huv : W.toAffine.Nonsingular u v, E (bc S) = WeierstrassCurve.Affine.Point.some u v huv := by
    intro S u v hS
    obtain ⟨χ, hχ, hu, hv⟩ := hS
    have hfac : (bc S).1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W := by
      rw [bc_val]; exact hχ
    obtain ⟨huv, he⟩ := hevc K (bc S) χ hfac
    subst hu hv
    exact ⟨huv, he⟩
  cases hR' : E (bc R) with
  | zero =>
      exact absurd (bc_injective (E.injective (hR'.trans (E_bc_one (𝒢 K W hΔ) E hE).symm))) hR
  | some x y hxy =>
      obtain ⟨S, hS⟩ := ((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x y).mp
        (And.left hxy)
      obtain ⟨hxy', he⟩ := hread S x y hS
      have hRS : R = S := bc_injective (E.injective (hR'.trans he.symm))
      exact ⟨x, y, hRS ▸ hS⟩

theorem field_through {A₀ : Type} [CommRing A₀] (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent)
    (h𝒢O : 𝒢.IsOriginIdentity) (q : ℕ) [Fact q.Prime] {K : Type} [Field K] [Algebra A₀ K] (hqK : (q : K) ≠ 0)
    (W : WeierstrassCurve.Projective K) (hΔ : IsUnit W.Δ) (P Q : Section W)
    (h : IsDrinfeldBasis (𝒢 K W hΔ) q P Q) :
    (∃ x y : K, IsSectionThrough P x y) ∧ (∃ x y : K, IsSectionThrough Q x y) := by
  obtain ⟨ev, hev⟩ := h𝒢 K W hΔ
  obtain ⟨hP, hQ⟩ := ne_one_of_isDrinfeldBasis W hΔ (𝒢 K W hΔ) ev hev q hqK P Q h
  exact ⟨exists_isSectionThrough_of_ne_one 𝒢 h𝒢O W hΔ P hP, exists_isSectionThrough_of_ne_one 𝒢 h𝒢O W hΔ Q hQ⟩

end FieldCase

section Fibres

theorem base_mem_range_of_fibre {T K : Type} [CommRing T] [CommRing K] (W : WeierstrassCurve.Projective T)
    (g : T →+* K) (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map g))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W g φ)
    (p : Spec (CommRingCat.of T) ⟶ projModelCR W)
    (p' : Spec (CommRingCat.of K) ⟶ projModelCR (W.map g)) (χ' : ZChartRing (W.map g) →+* K)
    (hp' : p' = Spec.map (CommRingCat.ofHom χ') ≫ zChartι (W.map g))
    (hsq : p' ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom g) ≫ p)
    (z : Spec (CommRingCat.of K)) :
    p.base ((Spec.map (CommRingCat.ofHom g)).base z) ∈ Set.range (zChartι W).base := by
  have e : φ (coord W 2) = coord (W.map g) 2 := hcoef.2 2
  have hopen : Set.range (zChartι W).base = ((Proj.basicOpen (projModelGradingCR W) (coord W 2)) : Set _) := by
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
  have hopen' : Set.range (zChartι (W.map g)).base =
      ((Proj.basicOpen (projModelGradingCR (W.map g)) (coord (W.map g) 2)) : Set _) := by
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
  have h1 : p.base ((Spec.map (CommRingCat.ofHom g)).base z) = (Proj.map φ hφ).base (p'.base z) := by
    change (Spec.map (CommRingCat.ofHom g) ≫ p).base z = (p' ≫ Proj.map φ hφ).base z
    rw [hsq]
  have h2 : p'.base z ∈ ((Proj.basicOpen (projModelGradingCR (W.map g)) (coord (W.map g) 2)) : Set _) := by
    rw [← hopen', hp']
    exact ⟨(Spec.map (CommRingCat.ofHom χ')).base z, rfl⟩
  have h3 : p'.base z ∈ (Proj.map φ hφ ⁻¹ᵁ Proj.basicOpen (projModelGradingCR W) (coord W 2) : Set _) := by
    rw [Proj.map_preimage_basicOpen, e]
    exact h2
  rw [h1, hopen]
  exact h3

theorem exists_isSectionThrough_of_forall_mem_range {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (S : Section W) (h : ∀ t : Spec (CommRingCat.of T), S.1.base t ∈ Set.range (zChartι W).base) :
    ∃ x y : T, IsSectionThrough S x y := by
  have hrange : Set.range S.1.base ⊆ Set.range (zChartι W).base := by
    rintro _ ⟨t, rfl⟩
    exact h t
  let g : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (ZChartRing W)) := IsOpenImmersion.lift (zChartι W) S.1 hrange
  have hg : g ≫ zChartι W = S.1 := IsOpenImmersion.lift_fac _ _ hrange
  let χ : ZChartRing W →+* T :=
    ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom.comp g.appTop.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ZChartRing W))).inv.hom
  have hχ : Spec.map (CommRingCat.ofHom χ) = g := by
    change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (ZChartRing W))).inv ≫ g.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of T)).hom) = g
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← Scheme.isoSpec_Spec_hom,
      Category.assoc, Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  exact ⟨affX χ, affY χ, χ, by rw [IsZChartSection, hχ, hg], rfl, rfl⟩

theorem fibre_mem_range {A₀ : Type} [CommRing A₀] (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent)
    (h𝒢O : 𝒢.IsOriginIdentity) (q : ℕ) [Fact q.Prime]
    {T K : Type} [CommRing T] [Field K] [Algebra A₀ K] (hqK : (q : K) ≠ 0)
    (W : WeierstrassCurve.Projective T) (g : T →+* K)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map g))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W g φ)
    (P Q : Section W) (y : RawDrinfeldPair K) (hc : y.curve = W.map g)
    (hlev : ∃ hΔ' : IsUnit y.curve.Δ, IsDrinfeldBasis (𝒢 K y.curve hΔ') q y.P y.Q)
    (hP : y.P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom g) ≫ P.1)
    (hQ : y.Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom g) ≫ Q.1)
    (z : Spec (CommRingCat.of K)) :
    P.1.base ((Spec.map (CommRingCat.ofHom g)).base z) ∈ Set.range (zChartι W).base ∧
    Q.1.base ((Spec.map (CommRingCat.ofHom g)).base z) ∈ Set.range (zChartι W).base := by
  obtain ⟨C', P', Q'⟩ := y
  change C' = W.map g at hc
  subst hc
  rw [eqToHom_refl, Category.id_comp] at hP hQ
  obtain ⟨hΔ', hDB⟩ := hlev
  obtain ⟨⟨u, v, χP, hχP, -, -⟩, ⟨u', v', χQ, hχQ, -, -⟩⟩ :=
    field_through 𝒢 h𝒢 h𝒢O q hqK (W.map g) hΔ' P' Q' hDB
  exact ⟨base_mem_range_of_fibre W g φ hφ hcoef P.1 P'.1 χP hχP hP z,
    base_mem_range_of_fibre W g φ hφ hcoef Q.1 Q'.1 χQ hχQ hQ z⟩

end Fibres

end WeierstrassCurve.DrinfeldGlobal.DrinfeldThrough

end

open WeierstrassCurve.DrinfeldGlobal.DrinfeldThrough in

theorem solution
    (q : ℕ) [Fact q.Prime] (A₀ : Type) [CommRing A₀]
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T : Type} [CommRing T] [Algebra A₀ T] (E : WeierstrassCurve T) (hq : IsUnit ((q : ℕ) : T))
    (x : RawDrinfeldPair T) (hx : RawDrinfeldPair.IsLevel 𝒢 q E x) :
    (∃ xP yP : T, IsSectionThrough x.P xP yP) ∧ (∃ xQ yQ : T, IsSectionThrough x.Q xQ yQ) := by
  classical

  have key : ∀ t : Spec (CommRingCat.of T),
      x.P.1.base t ∈ Set.range (zChartι x.curve).base ∧ x.Q.1.base t ∈ Set.range (zChartι x.curve).base := by
    intro t
    let κ : Type := t.asIdeal.ResidueField
    letI alg : Algebra A₀ κ := ((algebraMap T κ).comp (algebraMap A₀ T)).toAlgebra
    let f : T →ₐ[A₀] κ := ⟨algebraMap T κ, fun _ => rfl⟩
    have hf : f.toRingHom = algebraMap T κ := rfl
    have hqκ : ((q : ℕ) : κ) ≠ 0 := by
      have hu := hq.map (algebraMap T κ)
      rw [map_natCast] at hu
      exact hu.ne_zero

    let z : Spec (CommRingCat.of κ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum κ)
    have hz : (Spec.map (CommRingCat.ofHom f.toRingHom)).base z = t := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap T κ) ⊥ = t.asIdeal
      exact Ideal.ker_algebraMap_residueField t.asIdeal

    have hx' := 𝒯.isLevel_map f E x hx
    obtain ⟨hc, hpin⟩ := h𝒯.2 T κ f x
    obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom x.curve f.toRingHom
    obtain ⟨hPsq, hQsq⟩ := hpin φ hφ hcoef
    rw [← hz]
    exact fibre_mem_range 𝒢 h𝒢 h𝒢O q hqκ x.curve f.toRingHom φ hφ hcoef x.P x.Q (𝒯.map f x) hc hx'.2 hPsq hQsq z
  exact ⟨exists_isSectionThrough_of_forall_mem_range x.P fun t => (key t).1,
    exists_isSectionThrough_of_forall_mem_range x.Q fun t => (key t).2⟩

end S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit (solution)
