-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.groupLaws_eq_and_levelTransport_heq_of_isOriginIdentity_of_isSectionTransport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/309805a2-22d3-57a3-92c4-292170b2376a

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_groupLaws_eq_and_levelTransport_heq_of_isOriginIdentity_of_isSectionTransport

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2MKcLawTransportUnique

theorem relativeGroupLaw_ext {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)} (G G' : RelativeGroupLaw R f)
    (hone : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)), G.one s = G'.one s)
    (hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
      G.mul s x y = G'.mul s x y) :
    G = G' := by
  have hinv : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s f),
      G.inv s x = G'.inv s x := by
    intro S s x
    letI : Group (SchemeHomOver s f) := G'.pointGroup s
    have h : G.inv s x * x = 1 := by
      show G'.mul s (G.inv s x) x = G'.one s
      rw [← hmul, ← hone]
      exact G.inv_mul_cancel s x
    exact eq_inv_of_mul_eq_one_left h
  obtain ⟨mul, one, inv, _, _, _, _, _⟩ := G
  obtain ⟨mul', one', inv', _, _, _, _, _⟩ := G'
  have e1 : @mul = @mul' := by
    funext S s x y
    exact hmul s x y
  have e2 : @one = @one' := by
    funext S s
    exact hone s
  have e3 : @inv = @inv' := by
    funext S s x
    exact hinv s x
  subst e1 e2 e3
  rfl

theorem rawDrinfeldPair_ext {T : Type u} [CommRing T] (r r' : RawDrinfeldPair T) (hc : r.curve = r'.curve)
    (hP : r.P.1 ≫ eqToHom (congrArg projModelCR hc) = r'.P.1)
    (hQ : r.Q.1 ≫ eqToHom (congrArg projModelCR hc) = r'.Q.1) : r = r' := by
  obtain ⟨c, P, Q⟩ := r
  obtain ⟨c', P', Q'⟩ := r'
  dsimp only at hc
  subst hc
  simp only [eqToHom_refl, Category.comp_id] at hP hQ
  cases Subtype.ext hP
  cases Subtype.ext hQ
  rfl

theorem levelTransport_ext {A : Type u} [CommRing A] {𝒢 : GroupLaws A} {q : ℕ} (𝒯 𝒯' : LevelTransport A 𝒢 q)
    (hmap : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (x : RawDrinfeldPair T), 𝒯.map f x = 𝒯'.map f x)
    (hact : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
      (x : RawDrinfeldPair T), 𝒯.act C x = 𝒯'.act C x) :
    𝒯 = 𝒯' := by
  obtain ⟨map, act, _, _, _, _, _, _, _⟩ := 𝒯
  obtain ⟨map', act', _, _, _, _, _, _, _⟩ := 𝒯'
  have e1 : @map = @map' := by
    funext T T' _ _ _ _ f x
    exact hmap f x
  have e2 : @act = @act' := by
    funext T _ _ C x
    exact hact C x
  subst e1 e2
  rfl

section Identity

variable (A : Type u) [CommRing A] {T : Type u} [CommRing T] [Algebra A T]

theorem eq_id_of_isCoefficientHom_id (W : WeierstrassCurve.Projective T)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map (AlgHom.id A T).toRingHom))
    (hcoef : IsCoefficientHom W (AlgHom.id A T).toRingHom φ) :
    φ = GradedRingHom.id (projModelGradingCR W) := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have key : φ.toRingHom.comp (Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal) =
      Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal := by
    apply MvPolynomial.ringHom_ext
    · intro a
      exact hcoef.1 a
    · intro i
      exact hcoef.2 i
  exact RingHom.congr_fun key p

theorem projMap_eq_id (W : WeierstrassCurve.Projective T)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map (AlgHom.id A T).toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (AlgHom.id A T).toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W (AlgHom.id A T).toRingHom φ) :
    Proj.map φ hφ = 𝟙 (projModelCR W) := by
  obtain rfl := eq_id_of_isCoefficientHom_id A W φ hcoef
  exact Proj.map_id

theorem specMap_id : Spec.map (CommRingCat.ofHom (AlgHom.id A T).toRingHom) = 𝟙 (Spec (CommRingCat.of T)) := by
  change Spec.map (CommRingCat.ofHom (RingHom.id T)) = 𝟙 _
  rw [CommRingCat.ofHom_id, Spec.map_id]

end Identity

theorem mul_val_congr {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {S : Scheme.{u}} {s s' : S ⟶ Spec (CommRingCat.of R)} (e : s = s')
    (x y : SchemeHomOver s f) (x' y' : SchemeHomOver s' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (G.mul s x y).1 = (G.mul s' x' y').1 := by
  subst e
  cases Subtype.ext hx
  cases Subtype.ext hy
  rfl

theorem law_eq (A : Type u) [CommRing A] {T : Type u} [CommRing T] [Algebra A T]
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (G G' : RelativeGroupLaw T (projModelStrCR W))
    (χ : OriginChartRing W →+* T) (hχ : IsOriginChartSection (G.one (𝟙 _)) χ)
    (hχx : χ (xOverY W) = 0) (hχz : χ (zOverY W) = 0)
    (χ' : OriginChartRing W →+* T) (hχ' : IsOriginChartSection (G'.one (𝟙 _)) χ')
    (hχ'x : χ' (xOverY W) = 0) (hχ'z : χ' (zOverY W) = 0)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map (AlgHom.id A T).toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (AlgHom.id A T).toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W (AlgHom.id A T).toRingHom φ) :
    G = G' := by
  haveI : W.toAffine.IsElliptic := ⟨hΔ⟩

  change projModelGradingCR W →+*ᵍ projModelGradingCR W at φ
  change HomogeneousIdeal.irrelevant (projModelGradingCR W) ≤
    (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ at hφ
  have hmap : Proj.map φ hφ = 𝟙 (projModelCR W) := projMap_eq_id A W φ hφ hcoef
  have hspec : Spec.map (CommRingCat.ofHom (AlgHom.id A T).toRingHom) = 𝟙 (Spec (CommRingCat.of T)) :=
    specMap_id A

  have h1 : (G'.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom (AlgHom.id A T).toRingHom) ≫ (G.one (𝟙 (Spec (CommRingCat.of T)))).1 :=
    comp_projMap_eq_of_isOriginChartSection W (AlgHom.id A T).toRingHom φ hφ hcoef
      (G.one (𝟙 _)) (G'.one (𝟙 _)) χ hχ hχx hχz χ' hχ' hχ'x hχ'z
  have hone₀ : (G.one (𝟙 (Spec (CommRingCat.of T)))).1 = (G'.one (𝟙 (Spec (CommRingCat.of T)))).1 := by
    have h := h1
    rw [hmap, hspec, Category.comp_id, Category.id_comp] at h
    exact h.symm

  have hsq : Proj.map φ hφ ≫ projModelStrCR W =
      projModelStrCR W ≫ Spec.map (CommRingCat.ofHom (AlgHom.id A T).toRingHom) := by
    rw [hmap, hspec, Category.id_comp]
    exact (Category.comp_id _).symm

  have K : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver s (projModelStrCR W)),
      (G'.mul s x y).1 ≫ Proj.map φ hφ =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom (AlgHom.id A T).toRingHom))
          ⟨x.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, y.2]⟩).1 :=
    fun s x y =>
      comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq W (AlgHom.id A T).toRingHom φ hφ hcoef G G' h1 hsq s x y
  apply relativeGroupLaw_ext
  · intro S s
    have e := (G.one_natural (𝟙 _) s s (Category.comp_id s)).symm
    have e' := (G'.one_natural (𝟙 _) s s (Category.comp_id s)).symm
    apply Subtype.ext
    rw [e, e', schemeHomOverComp_coe, schemeHomOverComp_coe, hone₀]
  · intro S s x y
    apply Subtype.ext
    have h := K s x y
    have hs : s = s ≫ Spec.map (CommRingCat.ofHom (AlgHom.id A T).toRingHom) := by
      rw [hspec, Category.comp_id]
    have hx : x.1 = x.1 ≫ Proj.map φ hφ := by rw [hmap, Category.comp_id]
    have hy : y.1 = y.1 ≫ Proj.map φ hφ := by rw [hmap, Category.comp_id]
    rw [← mul_val_congr G hs x y _ _ hx hy, hmap, Category.comp_id] at h
    exact h.symm

theorem eqToHom_comp_projModelStrCR {T : Type u} [CommRing T] {c c' : WeierstrassCurve.Projective T} (e : c = c') :
    eqToHom (congrArg projModelCR e) ≫ projModelStrCR c' = projModelStrCR c := by
  subst e
  simp

theorem section_eq_of_cartesian {T T' : Type u} [CommRing T] [CommRing T'] (V : WeierstrassCurve.Projective T)
    (f : T →+* T') (φ : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (V.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR V)).map φ)
    (hcoef : IsCoefficientHom V f φ)
    {c c' : WeierstrassCurve.Projective T'} (e : c = V.map f) (e' : c' = V.map f)
    (P : Section c) (P' : Section c')
    (h : P.1 ≫ eqToHom (congrArg projModelCR e) ≫ Proj.map φ hφ =
      P'.1 ≫ eqToHom (congrArg projModelCR e') ≫ Proj.map φ hφ) :
    P.1 ≫ eqToHom (congrArg projModelCR (e.trans e'.symm)) = P'.1 := by
  subst e
  subst e'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
  have pb := isPullback_projMap_of_isCoefficientHom V f φ hφ hcoef
  refine pb.hom_ext h ?_
  rw [P.2, P'.2]

theorem section_eq_of_mono {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)
    {c c' : WeierstrassCurve.Projective T} (e : c = V) (e' : c' = V)
    (P : Section c) (P' : Section c') {Z : Scheme.{u}} (g : projModelCR V ⟶ Z) [Mono g]
    (h : P.1 ≫ eqToHom (congrArg projModelCR e) ≫ g = P'.1 ≫ eqToHom (congrArg projModelCR e') ≫ g) :
    P.1 ≫ eqToHom (congrArg projModelCR (e.trans e'.symm)) = P'.1 := by
  subst e
  subst e'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
  exact (cancel_mono g).mp h

theorem transport_eq (A : Type u) [CommRing A] (q : ℕ) (𝒢 : GroupLaws A)
    (𝒯 𝒯' : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport) (h𝒯' : 𝒯'.IsSectionTransport)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :
    𝒯 = 𝒯' := by
  apply levelTransport_ext
  · intro T T' _ _ _ _ f x
    obtain ⟨hc, H⟩ := h𝒯.2 T T' f x
    obtain ⟨hc', H'⟩ := h𝒯'.2 T T' f x
    obtain ⟨φ, hφ, hcoef⟩ := hCO T T' f x.curve
    obtain ⟨hP, hQ⟩ := H φ hφ hcoef
    obtain ⟨hP', hQ'⟩ := H' φ hφ hcoef
    refine rawDrinfeldPair_ext _ _ (hc.trans hc'.symm) ?_ ?_
    · exact section_eq_of_cartesian x.curve f.toRingHom φ hφ hcoef hc hc' _ _ (hP.trans hP'.symm)
    · exact section_eq_of_cartesian x.curve f.toRingHom φ hφ hcoef hc hc' _ _ (hQ.trans hQ'.symm)
  · intro T _ _ C x
    obtain ⟨hc, H⟩ := h𝒯.1 T C x
    obtain ⟨hc', H'⟩ := h𝒯'.1 T C x
    obtain ⟨φ, hφ, hvc, hiso, -⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap x.curve C
    obtain ⟨hP, hQ⟩ := H φ hφ hvc
    obtain ⟨hP', hQ'⟩ := H' φ hφ hvc
    refine rawDrinfeldPair_ext _ _ (hc.trans hc'.symm) ?_ ?_
    · exact section_eq_of_mono (C • x.curve) hc hc' _ _ (Proj.map φ hφ) (hP.trans hP'.symm)
    · exact section_eq_of_mono (C • x.curve) hc hc' _ _ (Proj.map φ hφ) (hQ.trans hQ'.symm)

end P2MKcLawTransportUnique

set_option linter.unusedVariables false in
open P2MKcLawTransportUnique in

theorem solution
    (A : Type u) [CommRing A] (q : ℕ)
    (𝒢 𝒢' : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity) (h𝒢O' : 𝒢'.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (𝒯' : LevelTransport A 𝒢' q) (h𝒯 : 𝒯.IsSectionTransport) (h𝒯' : 𝒯'.IsSectionTransport)

    (hVC : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :
    𝒢 = 𝒢' ∧ HEq 𝒯 𝒯' := by
  have h𝒢 : 𝒢 = 𝒢' := by
    funext T _ _ W hΔ
    obtain ⟨χ, hχ, hχx, hχz⟩ := h𝒢O T W hΔ
    obtain ⟨χ', hχ', hχ'x, hχ'z⟩ := h𝒢O' T W hΔ
    obtain ⟨φ, hφ, hcoef⟩ := hCO T T (AlgHom.id A T) W
    exact law_eq A W hΔ (𝒢 T W hΔ) (𝒢' T W hΔ) χ hχ hχx hχz χ' hχ' hχ'x hχ'z φ hφ hcoef
  subst h𝒢
  exact ⟨rfl, heq_of_eq (transport_eq A q 𝒢 𝒯 𝒯' h𝒯 h𝒯' hCO)⟩

end S_WeierstrassCurve_DrinfeldGlobal_groupLaws_eq_and_levelTransport_heq_of_isOriginIdentity_of_isSectionTransport
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_groupLaws_eq_and_levelTransport_heq_of_isOriginIdentity_of_isSectionTransport (solution)
