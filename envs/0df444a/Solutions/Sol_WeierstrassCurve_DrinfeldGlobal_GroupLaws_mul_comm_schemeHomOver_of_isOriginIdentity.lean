-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comm_schemeHomOver_of_isOriginIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5a8a5f1f-d692-57a1-bed5-59f82c400cbe

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_of_isOriginIdentity
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_of_isOriginChartSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_schemeHomOver_of_isOriginIdentity
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace LawCommOnPointsBody

theorem mul_val_congr {T : Type} [CommRing T] {E : Scheme.{0}} {p : E ⟶ Spec (CommRingCat.of T)}
    (G : RelativeGroupLaw T p) {S : Scheme.{0}} {t t' : S ⟶ Spec (CommRingCat.of T)} (h : t = t')
    (x y : SchemeHomOver t p) (x' y' : SchemeHomOver t' p) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (G.mul t x y).1 = (G.mul t' x' y').1 := by
  subst h
  have hx' : x = x' := Subtype.ext hx
  have hy' : y = y' := Subtype.ext hy
  subst hx' hy'
  rfl

theorem hVC_of_shelf (A : Type) [CommRing A] :
    ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T)
      (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ := by
  intro T _ _ W C
  obtain ⟨φ, hφ, h, -, -⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap W C
  exact ⟨φ, hφ, h⟩

theorem hCO_of_shelf (A : Type) [CommRing A] :
    ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ :=
  fun _ _ _ _ _ _ f W => WeierstrassProjModel.exists_isCoefficientHom W f.toRingHom

theorem affine_case (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent)
    (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (R : Type) [CommRing R] (f : T →+* R)
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR W)) :
    ((𝒢 T W hΔ).mul _ x y).1 = ((𝒢 T W hΔ).mul _ y x).1 := by
  classical
  haveI : W.toAffine.IsElliptic := ⟨hΔ⟩

  have hΔ' : IsUnit (W.map f).Δ := by
    rw [WeierstrassCurve.map_Δ]; exact hΔ.map f
  letI : Algebra A R := (f.comp (algebraMap A T)).toAlgebra

  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom W f
  have hpb := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W f φ hφ hcoef
  have hsq : Proj.map φ hφ ≫ projModelStrCR W =
      projModelStrCR (W.map f) ≫ Spec.map (CommRingCat.ofHom f) := hpb.w

  obtain ⟨χ, hχ, hχx, hχz⟩ := h𝒢O T W hΔ
  obtain ⟨χ', hχ', hχ'x, hχ'z⟩ := h𝒢O R (W.map f) hΔ'
  have h1 : ((𝒢 R (W.map f) hΔ').one (𝟙 _)).1 ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom f) ≫ ((𝒢 T W hΔ).one (𝟙 _)).1 :=
    WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_of_isOriginChartSection W f φ hφ hcoef
      ((𝒢 T W hΔ).one (𝟙 _)) ((𝒢 R (W.map f) hΔ').one (𝟙 _)) χ hχ hχx hχz χ' hχ' hχ'x hχ'z

  have wx : x.1 ≫ projModelStrCR W = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom f) := by
    rw [x.2, Category.id_comp]
  have wy : y.1 ≫ projModelStrCR W = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom f) := by
    rw [y.2, Category.id_comp]
  let xs : Section (W.map f) := ⟨hpb.lift x.1 (𝟙 _) wx, hpb.lift_snd _ _ _⟩
  let ys : Section (W.map f) := ⟨hpb.lift y.1 (𝟙 _) wy, hpb.lift_snd _ _ _⟩
  have hxs : xs.1 ≫ Proj.map φ hφ = x.1 := hpb.lift_fst _ _ _
  have hys : ys.1 ≫ Proj.map φ hφ = y.1 := hpb.lift_fst _ _ _

  have hsec : (𝒢 R (W.map f) hΔ').mul _ xs ys = (𝒢 R (W.map f) hΔ').mul _ ys xs :=
    WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comm_of_isOriginIdentity 𝒢 h𝒢 h𝒢O
      (hVC_of_shelf A) (hCO_of_shelf A) R (W.map f) hΔ' xs ys

  have hK := fun (a b : Section (W.map f)) =>
    WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq W f φ hφ hcoef
      (𝒢 T W hΔ) (𝒢 R (W.map f) hΔ') h1 hsq (𝟙 _) a b

  let xt : SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom f)) (projModelStrCR W) :=
    ⟨xs.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, xs.2]⟩
  let yt : SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom f)) (projModelStrCR W) :=
    ⟨ys.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, ys.2]⟩
  have e1 : ((𝒢 T W hΔ).mul _ x y).1 = ((𝒢 T W hΔ).mul _ xt yt).1 :=
    mul_val_congr (𝒢 T W hΔ) (Category.id_comp _).symm x y xt yt hxs.symm hys.symm
  have e2 : ((𝒢 T W hΔ).mul _ yt xt).1 = ((𝒢 T W hΔ).mul _ y x).1 :=
    mul_val_congr (𝒢 T W hΔ) (Category.id_comp _) yt xt y x hys hxs
  calc ((𝒢 T W hΔ).mul _ x y).1
      = ((𝒢 T W hΔ).mul _ xt yt).1 := e1
    _ = ((𝒢 R (W.map f) hΔ').mul _ xs ys).1 ≫ Proj.map φ hφ := (hK xs ys).symm
    _ = ((𝒢 R (W.map f) hΔ').mul _ ys xs).1 ≫ Proj.map φ hφ := by rw [hsec]
    _ = ((𝒢 T W hΔ).mul _ yt xt).1 := hK ys xs
    _ = ((𝒢 T W hΔ).mul _ y x).1 := e2

theorem spec_case (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent)
    (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (R : CommRingCat.{0}) (t : Spec R ⟶ Spec (CommRingCat.of T))
    (x y : SchemeHomOver t (projModelStrCR W)) :
    ((𝒢 T W hΔ).mul t x y).1 = ((𝒢 T W hΔ).mul t y x).1 := by
  obtain ⟨φ₀, rfl⟩ : ∃ φ₀ : CommRingCat.of T ⟶ R, t = Spec.map φ₀ :=
    ⟨Spec.preimage t, (Spec.map_preimage t).symm⟩
  exact affine_case A 𝒢 h𝒢 h𝒢O T W hΔ R φ₀.hom x y

end LawCommOnPointsBody

open LawCommOnPointsBody in
theorem solution
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W)) :
    (𝒢 T W hΔ).mul t x y = (𝒢 T W hΔ).mul t y x := by
  apply Subtype.ext
  refine Scheme.Cover.hom_ext S.affineCover _ _ fun j => ?_
  have e1 := congrArg Subtype.val ((𝒢 T W hΔ).mul_natural t (S.affineCover.f j ≫ t) (S.affineCover.f j) rfl x y)
  have e2 := congrArg Subtype.val ((𝒢 T W hΔ).mul_natural t (S.affineCover.f j ≫ t) (S.affineCover.f j) rfl y x)
  simp only [schemeHomOverComp_coe] at e1 e2
  rw [e1, e2]
  exact spec_case A 𝒢 h𝒢 h𝒢O T W hΔ _ (S.affineCover.f j ≫ t) _ _

end S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_schemeHomOver_of_isOriginIdentity
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_schemeHomOver_of_isOriginIdentity (solution)
