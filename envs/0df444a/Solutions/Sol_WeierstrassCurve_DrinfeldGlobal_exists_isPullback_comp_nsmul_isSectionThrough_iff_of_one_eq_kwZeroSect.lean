-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/cf2bd833-59b3-5649-887b-c81fe7ce4c77

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect

set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace KTRing
namespace Transport

section Chart

variable {B T : Type} [CommRing B] [CommRing T] (V : WeierstrassCurve.Projective B) (f : B →+* T)
  (φ : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map f))
  (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (V.map f)) ≤
    (HomogeneousIdeal.irrelevant (projModelGradingCR V)).map φ)
  (hcoef : IsCoefficientHom V f φ)

theorem isSectionThrough_iff_of_eq (S : Section (V.map f)) (x y : T)
    (s₀ s₁ s₂ : ProjModelRingCR (V.map f))
    (e₀ : s₀ = coord (V.map f) 0) (e₁ : s₁ = coord (V.map f) 1) (e₂ : s₂ = coord (V.map f) 2)
    (h₂ : s₂ ∈ projModelGradingCR (V.map f) 1)
    (h₀ : s₀ ∈ projModelGradingCR (V.map f) (1 • 1)) (h₁ : s₁ ∈ projModelGradingCR (V.map f) (1 • 1)) :
    IsSectionThrough S x y ↔
      ∃ χ : Away (projModelGradingCR (V.map f)) s₂ →+* T,
        S.1 = Spec.map (CommRingCat.ofHom χ) ≫ Proj.awayι (projModelGradingCR (V.map f)) s₂ h₂ one_pos ∧
        χ (Away.mk (projModelGradingCR (V.map f)) h₂ 1 s₀ h₀) = x ∧
        χ (Away.mk (projModelGradingCR (V.map f)) h₂ 1 s₁ h₁) = y := by
  subst e₀ e₁ e₂
  rfl

theorem awayι_comp_projMap :
    Proj.awayι (projModelGradingCR (V.map f)) (φ (coord V 2)) (φ.2 (coord_mem V 2)) one_pos ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom (Away.map φ (coord V 2))) ≫ zChartι V :=
  Proj.awayι_comp_map φ hφ one_pos (coord V 2) (coord_mem V 2)

include hcoef in

theorem isSectionThrough_iff_comp_projMap (S : Section (V.map f)) (x y : T) :
    IsSectionThrough S x y ↔
      ∃ χ : ZChartRing V →+* T, S.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom χ) ≫ zChartι V ∧
        χ (xOverZ V) = x ∧ χ (yOverZ V) = y := by
  have h₂ : φ (coord V 2) ∈ projModelGradingCR (V.map f) 1 := φ.2 (coord_mem V 2)
  have h₀ : φ (coord V 0) ∈ projModelGradingCR (V.map f) (1 • 1) := by simpa using φ.2 (coord_mem V 0)
  have h₁ : φ (coord V 1) ∈ projModelGradingCR (V.map f) (1 • 1) := by simpa using φ.2 (coord_mem V 1)
  rw [isSectionThrough_iff_of_eq V f S x y (φ (coord V 0)) (φ (coord V 1)) (φ (coord V 2))
    (hcoef.2 0) (hcoef.2 1) (hcoef.2 2) h₂ h₀ h₁]
  have hmkx : Away.map φ (coord V 2) (xOverZ V) = Away.mk (projModelGradingCR (V.map f)) h₂ 1 (φ (coord V 0)) h₀ := by
    rw [xOverZ, Away.map_mk]
  have hmky : Away.map φ (coord V 2) (yOverZ V) = Away.mk (projModelGradingCR (V.map f)) h₂ 1 (φ (coord V 1)) h₁ := by
    rw [yOverZ, Away.map_mk]
  constructor
  · rintro ⟨χ₁, hS, hx, hy⟩
    refine ⟨χ₁.comp (Away.map φ (coord V 2)), ?_, ?_, ?_⟩
    · rw [hS, Category.assoc, awayι_comp_projMap V f φ hφ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [RingHom.comp_apply, hmkx, hx]
    · rw [RingHom.comp_apply, hmky, hy]
  · rintro ⟨χ₀, hS, hx, hy⟩

    have hrange : Set.range S.1.base ⊆
        Set.range (Proj.awayι (projModelGradingCR (V.map f)) (φ (coord V 2)) h₂ one_pos).base := by
      rintro p ⟨t, rfl⟩
      have hp : (S.1 ≫ Proj.map φ hφ).base t ∈ (zChartι V).opensRange := by
        rw [hS]; exact ⟨(Spec.map (CommRingCat.ofHom χ₀)).base t, rfl⟩
      rw [Proj.opensRange_awayι] at hp
      have hp' : S.1.base t ∈ Proj.map φ hφ ⁻¹ᵁ Proj.basicOpen (projModelGradingCR V) (coord V 2) := hp
      rw [Proj.map_preimage_basicOpen, ← Proj.opensRange_awayι _ _ h₂ one_pos] at hp'
      exact hp'
    set l := IsOpenImmersion.lift _ _ hrange with hl
    have hlS : l ≫ Proj.awayι (projModelGradingCR (V.map f)) (φ (coord V 2)) h₂ one_pos = S.1 :=
      IsOpenImmersion.lift_fac _ _ hrange
    obtain ⟨χ₁, hχ₁⟩ := Spec.map_surjective l
    refine ⟨χ₁.hom, ?_, ?_, ?_⟩
    · rw [CommRingCat.ofHom_hom, hχ₁, hlS]
    all_goals

      have hcmp : Spec.map (CommRingCat.ofHom χ₀) ≫ zChartι V =
          Spec.map (CommRingCat.ofHom (Away.map φ (coord V 2)) ≫ χ₁) ≫ zChartι V := by
        rw [← hS, ← hlS, ← hχ₁, Category.assoc, awayι_comp_projMap V f φ hφ, ← Category.assoc, ← Spec.map_comp]
      have heq : χ₀ = χ₁.hom.comp (Away.map φ (coord V 2)) := by
        have h1 := (cancel_mono (zChartι V)).mp hcmp
        have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
        simpa using h2
    · rw [← hmkx, ← RingHom.comp_apply, ← heq, hx]
    · rw [← hmky, ← RingHom.comp_apply, ← heq, hy]

end Chart

theorem mul_val_congr {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {S : Scheme.{0}} {s s' : S ⟶ Spec (CommRingCat.of R)} (e : s = s')
    (x y : SchemeHomOver s f) (x' y' : SchemeHomOver s' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (G.mul s x y).1 = (G.mul s' x' y').1 := by
  subst e
  cases Subtype.ext hx
  cases Subtype.ext hy
  rfl

end KTRing.Transport

open KTRing.Transport in
theorem solution {B T : Type} [CommRing B] [CommRing T] (V : WeierstrassCurve B) [V.IsElliptic] (f : B →+* T)
    (G : RelativeGroupLaw B (projModelStrCR V.toProjective)) (hG : (G.one (𝟙 _)).1 = (kwZeroSect B V).1)
    (L : RelativeGroupLaw T (projModelStrCR (V.map f).toProjective))
    (hL : (L.one (𝟙 _)).1 = (kwZeroSect T (V.map f)).1) :
    ∃ (Φ : projModelCR (V.map f).toProjective ⟶ projModelCR V.toProjective)
      (hsq : Φ ≫ projModelStrCR V.toProjective = projModelStrCR (V.map f).toProjective ≫ Spec.map (CommRingCat.ofHom f)),
      IsPullback Φ (projModelStrCR (V.map f).toProjective) (projModelStrCR V.toProjective)
        (Spec.map (CommRingCat.ofHom f)) ∧
      (∀ (n : ℕ) (S : Section (V.map f).toProjective),
        (L.nsmul (𝟙 _) n S).1 ≫ Φ =
          (G.nsmul (Spec.map (CommRingCat.ofHom f)) n
            ⟨S.1 ≫ Φ, by rw [Category.assoc, hsq, ← Category.assoc, S.2, Category.id_comp]⟩).1) ∧
      ((L.one (𝟙 _)).1 ≫ Φ = (G.one (Spec.map (CommRingCat.ofHom f))).1) ∧
      (∀ (S : Section (V.map f).toProjective) (x y : T),
        IsSectionThrough S x y ↔
          ∃ χ : ZChartRing V.toProjective →+* T, S.1 ≫ Φ = Spec.map (CommRingCat.ofHom χ) ≫ zChartι V.toProjective ∧
            χ (xOverZ V.toProjective) = x ∧ χ (yOverZ V.toProjective) = y) := by
  haveI : V.toProjective.toAffine.IsElliptic := ‹V.IsElliptic›
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom V.toProjective f
  have pb := isPullback_projMap_of_isCoefficientHom V.toProjective f φ hφ hcoef
  have hsq : Proj.map φ hφ ≫ projModelStrCR V.toProjective =
      projModelStrCR (V.map f).toProjective ≫ Spec.map (CommRingCat.ofHom f) := pb.w

  obtain ⟨χ, hχ, hχx, hχz⟩ :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect V G).mpr hG
  obtain ⟨χ', hχ', hχ'x, hχ'z⟩ :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect (V.map f) L).mpr hL
  have h1 : (L.one (𝟙 _)).1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 _)).1 :=
    comp_projMap_eq_of_isOriginChartSection V.toProjective f φ hφ hcoef (G.one (𝟙 _)) (L.one (𝟙 _))
      χ hχ hχx hχz χ' hχ' hχ'x hχ'z
  have hone : (L.one (𝟙 _)).1 ≫ Proj.map φ hφ = (G.one (Spec.map (CommRingCat.ofHom f))).1 := by
    rw [h1, ← G.one_natural (𝟙 _) (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom f)) (Category.comp_id _),
      schemeHomOverComp_coe]

  refine ⟨Proj.map φ hφ, hsq, pb, ?_, hone, ?_⟩
  · intro n S
    induction n with
    | zero => exact hone
    | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ,
        comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq V.toProjective f φ hφ hcoef G L h1 hsq (𝟙 _)
          (L.nsmul (𝟙 _) n S) S]
      exact mul_val_congr G (Category.id_comp _) _ _ _ _ ih rfl
  · intro S x y
    exact isSectionThrough_iff_comp_projMap V.toProjective f φ hφ hcoef S x y

end

end S_WeierstrassCurve_DrinfeldGlobal_exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect (solution)
