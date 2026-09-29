-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_hom_isFinite_flat_finrank_eq_of_map_map_eq_dualNumber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bdd62185-9663-5e19-b4d3-612bceb3ed0c

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_comp_projMap_eq_projMap_comp_isPullback_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_hom_isFinite_flat_finrank_eq_of_map_map_eq_dualNumber

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

namespace ConstVerschiebungAux

open MvPolynomial

section Generic

variable {T T' : Type} [CommRing T] [CommRing T']

theorem exists_coefHom (f : T →+* T') (W : WeierstrassCurve T) (W' : WeierstrassCurve T') (h : W.map f = W') :
    ∃ (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR W'.toProjective)
      (_ : HomogeneousIdeal.irrelevant (projModelGradingCR W'.toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ),
      (∀ a : T, φ (cls W.toProjective (C a)) = cls W'.toProjective (C (f a))) ∧
        ∀ i : Fin 3, φ (cls W.toProjective (X i)) = cls W'.toProjective (X i) := by
  subst h
  exact WeierstrassProjModel.exists_isCoefficientHom W.toProjective f

theorem isPullback_gen (f : T →+* T') (W : WeierstrassCurve T) (W' : WeierstrassCurve T') (h : W.map f = W')
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR W'.toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR W'.toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : (∀ a : T, φ (cls W.toProjective (C a)) = cls W'.toProjective (C (f a))) ∧
      ∀ i : Fin 3, φ (cls W.toProjective (X i)) = cls W'.toProjective (X i)) :
    IsPullback (Proj.map φ hφ) (projModelStrCR W'.toProjective) (projModelStrCR W.toProjective)
      (Spec.map (CommRingCat.ofHom f)) := by
  subst h
  exact WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W.toProjective f φ hφ hcoef

theorem exists_zChart_gen (f : T →+* T') (W : WeierstrassCurve T) (W' : WeierstrassCurve T') (h : W.map f = W')
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR W'.toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR W'.toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : (∀ a : T, φ (cls W.toProjective (C a)) = cls W'.toProjective (C (f a))) ∧
      ∀ i : Fin 3, φ (cls W.toProjective (X i)) = cls W'.toProjective (X i)) :
    ∃ a : ZChartRing W.toProjective →+* ZChartRing W'.toProjective,
      zChartι W'.toProjective ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ zChartι W.toProjective ∧
      a (xOverZ W.toProjective) = xOverZ W'.toProjective ∧ a (yOverZ W.toProjective) = yOverZ W'.toProjective := by
  subst h
  exact WeierstrassCurve.DrinfeldGlobal.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota W.toProjective f φ hφ hcoef

theorem exists_baseChange_gen (f : T →+* T')
    (W₁ W₂ : WeierstrassCurve T) (W₁' W₂' : WeierstrassCurve T') (h₁ : W₁.map f = W₁') (h₂ : W₂.map f = W₂')
    (u : projModelCR W₁.toProjective ⟶ projModelCR W₂.toProjective)
    (hu : u ≫ projModelStrCR W₂.toProjective = projModelStrCR W₁.toProjective)
    (φ₁ : projModelGradingCR W₁.toProjective →+*ᵍ projModelGradingCR W₁'.toProjective)
    (hφ₁ : HomogeneousIdeal.irrelevant (projModelGradingCR W₁'.toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₁.toProjective)).map φ₁)
    (hcoef₁ : (∀ a : T, φ₁ (cls W₁.toProjective (C a)) = cls W₁'.toProjective (C (f a))) ∧
      ∀ i : Fin 3, φ₁ (cls W₁.toProjective (X i)) = cls W₁'.toProjective (X i))
    (φ₂ : projModelGradingCR W₂.toProjective →+*ᵍ projModelGradingCR W₂'.toProjective)
    (hφ₂ : HomogeneousIdeal.irrelevant (projModelGradingCR W₂'.toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₂.toProjective)).map φ₂)
    (hcoef₂ : (∀ a : T, φ₂ (cls W₂.toProjective (C a)) = cls W₂'.toProjective (C (f a))) ∧
      ∀ i : Fin 3, φ₂ (cls W₂.toProjective (X i)) = cls W₂'.toProjective (X i)) :
    ∃ u' : projModelCR W₁'.toProjective ⟶ projModelCR W₂'.toProjective,
      u' ≫ projModelStrCR W₂'.toProjective = projModelStrCR W₁'.toProjective ∧
      u' ≫ Proj.map φ₂ hφ₂ = Proj.map φ₁ hφ₁ ≫ u ∧
      IsPullback u' (Proj.map φ₁ hφ₁) (Proj.map φ₂ hφ₂) u := by
  subst h₁ h₂
  obtain ⟨u', h1, h2, h3, -⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_comp_projMap_eq_projMap_comp_isPullback_of_isCoefficientHom f W₁ W₂ u hu
      φ₁ hφ₁ hcoef₁ φ₂ hφ₂ hcoef₂
  exact ⟨u', h1, h2, h3⟩

theorem kwZeroSect_comp_projMap (f : T →+* T') (W : WeierstrassCurve T) (W' : WeierstrassCurve T')
    (h : W.map f = W')
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR W'.toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR W'.toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : (∀ a : T, φ (cls W.toProjective (C a)) = cls W'.toProjective (C (f a))) ∧
      ∀ i : Fin 3, φ (cls W.toProjective (X i)) = cls W'.toProjective (X i)) :
    (kwZeroSect T' W').1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom f) ≫ (kwZeroSect T W).1 := by
  subst h
  obtain ⟨hχ, hx, hz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  obtain ⟨hχ', hx', hz'⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval (W.map f).toProjective
  exact WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_of_isOriginChartSection W.toProjective f φ hφ hcoef
    (kwZeroSect T W) (kwZeroSect T' (W.map f)) _ hχ hx hz _ hχ' hx' hz'

theorem eqToHom_comp_projModelStrCR (Y Y' : WeierstrassCurve T) (e : Y = Y') :
    eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective e)) ≫ projModelStrCR Y'.toProjective =
      projModelStrCR Y.toProjective := by
  subst e
  simp

theorem eqToHom_comp_projMap_eq_id (Y Y' : WeierstrassCurve T) (e : Y' = Y)
    (θ : projModelGradingCR Y.toProjective →+*ᵍ projModelGradingCR Y'.toProjective)
    (hθ : HomogeneousIdeal.irrelevant (projModelGradingCR Y'.toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR Y.toProjective)).map θ)
    (hC : ∀ a : T, θ (cls Y.toProjective (C a)) = cls Y'.toProjective (C a))
    (hX : ∀ i : Fin 3, θ (cls Y.toProjective (X i)) = cls Y'.toProjective (X i)) :
    eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective e)).symm ≫ Proj.map θ hθ = 𝟙 _ := by
  subst e
  have hid : θ = GradedRingHom.id _ := by
    apply DFunLike.ext
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    show θ (cls Y'.toProjective p) = cls Y'.toProjective p
    induction p using MvPolynomial.induction_on with
    | C a => exact hC a
    | add p q hp hq =>
        have e1 : cls Y'.toProjective (p + q) = cls Y'.toProjective p + cls Y'.toProjective q := map_add _ _ _
        rw [e1, map_add, hp, hq]
    | mul_X p i hp =>
        have e1 : cls Y'.toProjective (p * X i) = cls Y'.toProjective p * cls Y'.toProjective (X i) := map_mul _ _ _
        rw [e1, map_mul, hp, hX i]
  subst hid
  rw [eqToHom_refl, Category.id_comp]
  exact Proj.map_id

theorem projMap_eq_of_coefHom (f : T →+* T') (W : WeierstrassCurve T) (W' : WeierstrassCurve T')
    (φ φ' : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR W'.toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR W'.toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hφ' : HomogeneousIdeal.irrelevant (projModelGradingCR W'.toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ')
    (hc : (∀ a : T, φ (cls W.toProjective (C a)) = cls W'.toProjective (C (f a))) ∧
      ∀ i : Fin 3, φ (cls W.toProjective (X i)) = cls W'.toProjective (X i))
    (hc' : (∀ a : T, φ' (cls W.toProjective (C a)) = cls W'.toProjective (C (f a))) ∧
      ∀ i : Fin 3, φ' (cls W.toProjective (X i)) = cls W'.toProjective (X i)) :
    Proj.map φ hφ = Proj.map φ' hφ' := by
  have hid : φ = φ' := by
    apply DFunLike.ext
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    show φ (cls W.toProjective p) = φ' (cls W.toProjective p)
    induction p using MvPolynomial.induction_on with
    | C a => rw [hc.1 a, hc'.1 a]
    | add p q hp hq =>
        have e1 : cls W.toProjective (p + q) = cls W.toProjective p + cls W.toProjective q := map_add _ _ _
        rw [e1, map_add, map_add, hp, hq]
    | mul_X p i hp =>
        have e1 : cls W.toProjective (p * X i) = cls W.toProjective p * cls W.toProjective (X i) := map_mul _ _ _
        rw [e1, map_mul, map_mul, hp, hc.2 i, hc'.2 i]
  subst hid
  rfl

theorem one_comp_eq_one {X₁ X₂ : Scheme}
    {p₁ : X₁ ⟶ Spec (CommRingCat.of T)} {p₂ : X₂ ⟶ Spec (CommRingCat.of T)}
    (G₁ : RelativeGroupLaw T p₁) (G₂ : RelativeGroupLaw T p₂) (f : X₁ ⟶ X₂) (hf : f ≫ p₂ = p₁)
    (hfhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t p₁),
      (⟨(G₁.mul t x y).1 ≫ f, by rw [Category.assoc, hf]; exact (G₁.mul t x y).2⟩ : SchemeHomOver t p₂) =
        G₂.mul t ⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ ⟨y.1 ≫ f, by rw [Category.assoc, hf]; exact y.2⟩)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) :
    (G₁.one t).1 ≫ f = (G₂.one t).1 := by
  letI : Group (SchemeHomOver t p₂) := G₂.pointGroup t
  let a : SchemeHomOver t p₂ := ⟨(G₁.one t).1 ≫ f, by rw [Category.assoc, hf]; exact (G₁.one t).2⟩
  have h1 : (G₁.one t).1 ≫ f = (G₂.mul t a a).1 := by
    have h := congrArg Subtype.val (hfhom t (G₁.one t) (G₁.one t))
    rw [G₁.one_mul] at h
    exact h
  have h2 : a = a * a := Subtype.ext h1
  have h3 : a = 1 := by
    have h4 : a * 1 = a * a := by rw [mul_one]; exact h2
    exact (mul_left_cancel h4).symm
  exact congrArg Subtype.val h3

theorem zChartι_comp_projModelStrCR (W : WeierstrassCurve.Projective T) :
    zChartι W ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W) _).comp
        (algebraMap T ((projModelGradingCR W) 0)))) := by
  show Proj.awayι (projModelGradingCR W) (coord W 2) (coord_mem W 2) one_pos ≫ projModelStrCR W = _
  unfold projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem comp_scalar_eq_of_comp_eq {X : Scheme} {R T₀ : Type} [CommRing R] [CommRing T₀]
    (c : Spec (CommRingCat.of R) ⟶ X) (p : X ⟶ Spec (CommRingCat.of T₀))
    (s : T₀ →+* R) (hs : c ≫ p = Spec.map (CommRingCat.ofHom s))
    {B : Type} [CommRing B] (ρ : R →+* B) (b : T₀ →+* B)
    (h : Spec.map (CommRingCat.ofHom ρ) ≫ c ≫ p = Spec.map (CommRingCat.ofHom b)) :
    ρ.comp s = b := by
  have e : Spec.map (CommRingCat.ofHom (ρ.comp s)) = Spec.map (CommRingCat.ofHom b) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← hs, h]
  have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  simpa only [CommRingCat.hom_ofHom] using h'

theorem comp_eq_comp_of_square {X X' : Scheme} {R R' T₀ T₀' : Type} [CommRing R] [CommRing R'] [CommRing T₀]
    [CommRing T₀']
    (c : Spec (CommRingCat.of R) ⟶ X) (c' : Spec (CommRingCat.of R') ⟶ X') (Pr : X' ⟶ X)
    (p : X ⟶ Spec (CommRingCat.of T₀)) (p' : X' ⟶ Spec (CommRingCat.of T₀')) (f : T₀ →+* T₀')
    (hsq : Pr ≫ p = p' ≫ Spec.map (CommRingCat.ofHom f))
    (a : R →+* R') (ha : c' ≫ Pr = Spec.map (CommRingCat.ofHom a) ≫ c)
    (s : T₀ →+* R) (hs : c ≫ p = Spec.map (CommRingCat.ofHom s))
    (s' : T₀' →+* R') (hs' : c' ≫ p' = Spec.map (CommRingCat.ofHom s')) :
    a.comp s = s'.comp f := by
  have e : Spec.map (CommRingCat.ofHom (a.comp s)) = Spec.map (CommRingCat.ofHom (s'.comp f)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp, ← hs, ← hs',
      ← Category.assoc, ← ha, Category.assoc, hsq, Category.assoc]
  have h := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  simpa only [CommRingCat.hom_ofHom] using h

end Generic

section ChartGen
open HomogeneousLocalization HomogeneousIdealQuotientGrading
variable {T : Type} [CommRing T] (W : WeierstrassCurve.Projective T)

lemma coe_algebraMap_zero (t : T) :
    ((algebraMap T ((projModelGradingCR W) 0) t : (projModelGradingCR W) 0) : ProjModelRingCR W) = cls W (C t) := by
  rw [SetLike.GradeZero.coe_algebraMap]; rfl

lemma exists_coe_eq_cls_C (r : (projModelGradingCR W) 0) : ∃ t : T, (r : ProjModelRingCR W) = cls W (C t) := by
  obtain ⟨p, hp, hpr⟩ := (mem_quotGradingSubmodule_iff _ _).mp r.2
  have hp0 : p.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 p).mp hp
  refine ⟨p.coeff 0, ?_⟩
  rw [← hpr]
  by_cases h0 : p = 0
  · subst h0; simp [cls]
  · have htd : p.totalDegree = 0 := hp0.totalDegree h0
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at htd
    exact congrArg _ htd

lemma adjoin_range_coord_eq_top :
    Algebra.adjoin ((projModelGradingCR W) 0) (Set.range (coord W)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C t =>
      have : (Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (C t) : ProjModelRingCR W) =
          algebraMap ((projModelGradingCR W) 0) (ProjModelRingCR W) (algebraMap T ((projModelGradingCR W) 0) t) := by
        rw [SetLike.GradeZero.algebraMap_apply, coe_algebraMap_zero]
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

lemma mk_prod_pow_eq (a : ℕ) (ai : Fin 3 → ℕ) (hai : ai 0 + ai 1 + ai 2 = a)
    (x : ProjModelRingCR W) (hxeq : x = ∏ i, coord W i ^ ai i) (hx : x ∈ projModelGradingCR W (a • 1)) :
    Away.mk (projModelGradingCR W) (coord_mem W 2) a x hx = xOverZ W ^ ai 0 * yOverZ W ^ ai 1 := by
  apply val_injective
  simp only [val_mul, val_pow, xOverZ, yOverZ, Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow, hxeq, Fin.prod_univ_three]
  rw [← hai]
  ring

theorem ringHom_zChartRing_ext {B : Type} [CommRing B]
    (χ χ' : ZChartRing W →+* B)
    (hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      χ' (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)))
    (hx : χ (xOverZ W) = χ' (xOverZ W)) (hy : χ (yOverZ W) = χ' (yOverZ W)) :
    χ = χ' := by
  classical
  have hZ : coord W 2 ∈ projModelGradingCR W 1 := coord_mem W 2
  apply RingHom.ext
  intro z
  have hzs : z ∈ Submodule.span ((projModelGradingCR W) 0)
      { (Away.mk (projModelGradingCR W) hZ a (∏ i, coord W i ^ ai i)
          (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ coord_mem W i) : Away (projModelGradingCR W) (coord W 2)) |
        (a : ℕ) (ai : Fin 3 → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1) } := by
    rw [Away.span_mk_prod_pow_eq_top hZ (coord W) (adjoin_range_coord_eq_top W) (fun _ => 1) (fun i => coord_mem W i)]
    trivial
  induction hzs using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, ai, hai, rfl⟩ := hz
      have hai' : ai 0 + ai 1 + ai 2 = a := by simpa [Fin.sum_univ_three] using hai
      rw [mk_prod_pow_eq W a ai hai' _ rfl, map_mul, map_pow, map_pow, map_mul, map_pow, map_pow, hx, hy]
  | zero => simp
  | add x y _ _ hx' hy' => rw [map_add, map_add, hx', hy']
  | smul r x _ hx' =>
      obtain ⟨t, ht⟩ := exists_coe_eq_cls_C W r
      have hr : r = algebraMap T ((projModelGradingCR W) 0) t := Subtype.ext (by rw [ht, coe_algebraMap_zero])
      rw [Algebra.smul_def, HomogeneousLocalization.algebraMap_eq, map_mul, map_mul, hx', hr, hsc t]

end ChartGen

section Delegated

theorem hom_of_comp_projMap_eq
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    {T T' : Type} [CommRing T] [CommRing T'] [Algebra A T] [Algebra A T'] (f : T →+* T')
    (W₁ W₂ : WeierstrassCurve T) (hΔ₁ : IsUnit W₁.Δ) (hΔ₂ : IsUnit W₂.Δ)
    (W₁' W₂' : WeierstrassCurve T') (h₁ : W₁.map f = W₁') (h₂ : W₂.map f = W₂')
    (hΔ₁' : IsUnit W₁'.Δ) (hΔ₂' : IsUnit W₂'.Δ)
    (φ₁ : projModelGradingCR W₁.toProjective →+*ᵍ projModelGradingCR W₁'.toProjective)
    (hφ₁ : HomogeneousIdeal.irrelevant (projModelGradingCR W₁'.toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₁.toProjective)).map φ₁)
    (hcoef₁ : (∀ a : T, φ₁ (cls W₁.toProjective (MvPolynomial.C a)) = cls W₁'.toProjective (MvPolynomial.C (f a))) ∧
      ∀ i : Fin 3, φ₁ (cls W₁.toProjective (MvPolynomial.X i)) = cls W₁'.toProjective (MvPolynomial.X i))
    (φ₂ : projModelGradingCR W₂.toProjective →+*ᵍ projModelGradingCR W₂'.toProjective)
    (hφ₂ : HomogeneousIdeal.irrelevant (projModelGradingCR W₂'.toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₂.toProjective)).map φ₂)
    (hcoef₂ : (∀ a : T, φ₂ (cls W₂.toProjective (MvPolynomial.C a)) = cls W₂'.toProjective (MvPolynomial.C (f a))) ∧
      ∀ i : Fin 3, φ₂ (cls W₂.toProjective (MvPolynomial.X i)) = cls W₂'.toProjective (MvPolynomial.X i))
    (u : projModelCR W₁.toProjective ⟶ projModelCR W₂.toProjective)
    (hu : u ≫ projModelStrCR W₂.toProjective = projModelStrCR W₁.toProjective)
    (uhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W₁.toProjective)),
      (⟨((𝒢 T W₁ hΔ₁).mul t x y).1 ≫ u, by rw [Category.assoc, hu]; exact ((𝒢 T W₁ hΔ₁).mul t x y).2⟩ :
          SchemeHomOver t (projModelStrCR W₂.toProjective)) =
        (𝒢 T W₂ hΔ₂).mul t ⟨x.1 ≫ u, by rw [Category.assoc, hu]; exact x.2⟩ ⟨y.1 ≫ u, by rw [Category.assoc, hu]; exact y.2⟩)
    (u' : projModelCR W₁'.toProjective ⟶ projModelCR W₂'.toProjective)
    (hu' : u' ≫ projModelStrCR W₂'.toProjective = projModelStrCR W₁'.toProjective)
    (hsq : u' ≫ Proj.map φ₂ hφ₂ = Proj.map φ₁ hφ₁ ≫ u)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T')) (x y : SchemeHomOver t (projModelStrCR W₁'.toProjective)) :
    (⟨((𝒢 T' W₁' hΔ₁').mul t x y).1 ≫ u', by rw [Category.assoc, hu']; exact ((𝒢 T' W₁' hΔ₁').mul t x y).2⟩ :
        SchemeHomOver t (projModelStrCR W₂'.toProjective)) =
      (𝒢 T' W₂' hΔ₂').mul t ⟨x.1 ≫ u', by rw [Category.assoc, hu']; exact x.2⟩ ⟨y.1 ≫ u', by rw [Category.assoc, hu']; exact y.2⟩ := by
  subst h₁ h₂
  haveI : W₁.toProjective.toAffine.IsElliptic := ⟨hΔ₁⟩
  haveI : W₂.toProjective.toAffine.IsElliptic := ⟨hΔ₂⟩
  have hpb₂ : IsPullback (Proj.map φ₂ hφ₂) (projModelStrCR (W₂.map f).toProjective) (projModelStrCR W₂.toProjective)
      (Spec.map (CommRingCat.ofHom f)) :=
    WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W₂.toProjective f φ₂ hφ₂ hcoef₂
  have hsq₁ : Proj.map φ₁ hφ₁ ≫ projModelStrCR W₁.toProjective =
      projModelStrCR (W₁.map f).toProjective ≫ Spec.map (CommRingCat.ofHom f) :=
    (WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W₁.toProjective f φ₁ hφ₁ hcoef₁).w
  have hsq₂ : Proj.map φ₂ hφ₂ ≫ projModelStrCR W₂.toProjective =
      projModelStrCR (W₂.map f).toProjective ≫ Spec.map (CommRingCat.ofHom f) := hpb₂.w

  obtain ⟨χ₁, hχ₁, hχ₁x, hχ₁z⟩ := h𝒢O T W₁.toProjective hΔ₁
  obtain ⟨χ₁', hχ₁', hχ₁'x, hχ₁'z⟩ := h𝒢O T' (W₁.map f).toProjective hΔ₁'
  obtain ⟨χ₂, hχ₂, hχ₂x, hχ₂z⟩ := h𝒢O T W₂.toProjective hΔ₂
  obtain ⟨χ₂', hχ₂', hχ₂'x, hχ₂'z⟩ := h𝒢O T' (W₂.map f).toProjective hΔ₂'
  have h1₁ : ((𝒢 T' (W₁.map f) hΔ₁').one (𝟙 _)).1 ≫ Proj.map φ₁ hφ₁ =
      Spec.map (CommRingCat.ofHom f) ≫ ((𝒢 T W₁ hΔ₁).one (𝟙 _)).1 :=
    WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_of_isOriginChartSection W₁.toProjective f φ₁ hφ₁ hcoef₁
      ((𝒢 T W₁ hΔ₁).one (𝟙 _)) ((𝒢 T' (W₁.map f) hΔ₁').one (𝟙 _)) χ₁ hχ₁ hχ₁x hχ₁z χ₁' hχ₁' hχ₁'x hχ₁'z
  have h1₂ : ((𝒢 T' (W₂.map f) hΔ₂').one (𝟙 _)).1 ≫ Proj.map φ₂ hφ₂ =
      Spec.map (CommRingCat.ofHom f) ≫ ((𝒢 T W₂ hΔ₂).one (𝟙 _)).1 :=
    WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_of_isOriginChartSection W₂.toProjective f φ₂ hφ₂ hcoef₂
      ((𝒢 T W₂ hΔ₂).one (𝟙 _)) ((𝒢 T' (W₂.map f) hΔ₂').one (𝟙 _)) χ₂ hχ₂ hχ₂x hχ₂z χ₂' hχ₂' hχ₂'x hχ₂'z

  have H₁ : ∀ a b : SchemeHomOver t (projModelStrCR (W₁.map f).toProjective),
      ((𝒢 T' (W₁.map f) hΔ₁').mul t a b).1 ≫ Proj.map φ₁ hφ₁ =
        ((𝒢 T W₁ hΔ₁).mul (t ≫ Spec.map (CommRingCat.ofHom f))
          ⟨a.1 ≫ Proj.map φ₁ hφ₁, by rw [Category.assoc, hsq₁, ← Category.assoc, a.2]⟩
          ⟨b.1 ≫ Proj.map φ₁ hφ₁, by rw [Category.assoc, hsq₁, ← Category.assoc, b.2]⟩).1 :=
    fun a b => WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
      W₁.toProjective f φ₁ hφ₁ hcoef₁ (𝒢 T W₁ hΔ₁) (𝒢 T' (W₁.map f) hΔ₁') h1₁ hsq₁ t a b
  have H₂ : ∀ a b : SchemeHomOver t (projModelStrCR (W₂.map f).toProjective),
      ((𝒢 T' (W₂.map f) hΔ₂').mul t a b).1 ≫ Proj.map φ₂ hφ₂ =
        ((𝒢 T W₂ hΔ₂).mul (t ≫ Spec.map (CommRingCat.ofHom f))
          ⟨a.1 ≫ Proj.map φ₂ hφ₂, by rw [Category.assoc, hsq₂, ← Category.assoc, a.2]⟩
          ⟨b.1 ≫ Proj.map φ₂ hφ₂, by rw [Category.assoc, hsq₂, ← Category.assoc, b.2]⟩).1 :=
    fun a b => WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
      W₂.toProjective f φ₂ hφ₂ hcoef₂ (𝒢 T W₂ hΔ₂) (𝒢 T' (W₂.map f) hΔ₂') h1₂ hsq₂ t a b

  have U : ∀ a b : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom f)) (projModelStrCR W₁.toProjective),
      ((𝒢 T W₁ hΔ₁).mul (t ≫ Spec.map (CommRingCat.ofHom f)) a b).1 ≫ u =
        ((𝒢 T W₂ hΔ₂).mul (t ≫ Spec.map (CommRingCat.ofHom f)) ⟨a.1 ≫ u, by rw [Category.assoc, hu]; exact a.2⟩
          ⟨b.1 ≫ u, by rw [Category.assoc, hu]; exact b.2⟩).1 :=
    fun a b => congrArg Subtype.val (uhom (t ≫ Spec.map (CommRingCat.ofHom f)) a b)

  have key : ∀ (a b a' b' : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom f)) (projModelStrCR W₂.toProjective)),
      a.1 = a'.1 → b.1 = b'.1 →
        ((𝒢 T W₂ hΔ₂).mul (t ≫ Spec.map (CommRingCat.ofHom f)) a b).1 =
          ((𝒢 T W₂ hΔ₂).mul (t ≫ Spec.map (CommRingCat.ofHom f)) a' b').1 := by
    intro a b a' b' ha hb
    cases Subtype.ext ha
    cases Subtype.ext hb
    rfl
  apply Subtype.ext
  apply hpb₂.hom_ext
  · show (((𝒢 T' (W₁.map f) hΔ₁').mul t x y).1 ≫ u') ≫ Proj.map φ₂ hφ₂ =
      ((𝒢 T' (W₂.map f) hΔ₂').mul t _ _).1 ≫ Proj.map φ₂ hφ₂
    rw [Category.assoc, hsq, ← Category.assoc, H₁, U, H₂]
    refine key _ _ _ _ ?_ ?_ <;> simp only [Category.assoc, hsq]
  · have t1 : ∀ a b : SchemeHomOver t (projModelStrCR (W₁.map f).toProjective),
        ((𝒢 T' (W₁.map f) hΔ₁').mul t a b).1 ≫ projModelStrCR (W₁.map f).toProjective = t :=
      fun a b => ((𝒢 T' (W₁.map f) hΔ₁').mul t a b).2
    have t2 : ∀ a b : SchemeHomOver t (projModelStrCR (W₂.map f).toProjective),
        ((𝒢 T' (W₂.map f) hΔ₂').mul t a b).1 ≫ projModelStrCR (W₂.map f).toProjective = t :=
      fun a b => ((𝒢 T' (W₂.map f) hΔ₂').mul t a b).2
    show (((𝒢 T' (W₁.map f) hΔ₁').mul t x y).1 ≫ u') ≫ projModelStrCR (W₂.map f).toProjective =
      ((𝒢 T' (W₂.map f) hΔ₂').mul t _ _).1 ≫ projModelStrCR (W₂.map f).toProjective
    rw [t2, Category.assoc, hu', t1]

theorem isFinite_flat_lofp_surjective_finrank_of_isPullback {P X Y Z : Scheme} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (H : IsPullback fst snd f g)
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] [Surjective g]
    (m : ℕ) (hrk : ∀ z, g.finrank z = m) :
    IsFinite fst ∧ Flat fst ∧ LocallyOfFinitePresentation fst ∧ Surjective fst ∧ ∀ x, fst.finrank x = m := by
  have h1 : IsFinite fst := MorphismProperty.of_isPullback H.flip inferInstance
  have h2 : Flat fst := MorphismProperty.of_isPullback H.flip inferInstance
  have h3 : LocallyOfFinitePresentation fst := MorphismProperty.of_isPullback H.flip inferInstance
  have h4 : Surjective fst := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨h1, h2, h3, h4, fun x => ?_⟩
  have e : fst = H.isoPullback.hom ≫ pullback.fst f g := (H.isoPullback_hom_fst).symm
  rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_pullback_fst g f x, hrk]

end Delegated

end ConstVerschiebungAux

open ConstVerschiebungAux

set_option maxHeartbeats 6400000 in
theorem solution
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] [Algebra A (DualNumber k)] [CharP (DualNumber k) q]
    (W Wq : WeierstrassCurve (DualNumber k)) (hΔW : IsUnit W.Δ) (hΔq : IsUnit Wq.Δ)
    (Wq₀ : WeierstrassCurve k) (hconst : Wq₀.map (algebraMap k (DualNumber k)) = Wq)
    (W₀ : WeierstrassCurve k) (hW₀ : W.map (TrivSqZeroExt.fstHom k k k).toRingHom = W₀)
    (hΔ₀ : IsUnit (W₀.map (algebraMap k (DualNumber k))).Δ)
    (Vq : projModelCR Wq.toProjective ⟶ projModelCR W.toProjective)
    (hV : Vq ≫ projModelStrCR W.toProjective = projModelStrCR Wq.toProjective)
    (hVhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR Wq.toProjective)),
      (⟨((𝒢 (DualNumber k) Wq hΔq).mul t x y).1 ≫ Vq, by rw [Category.assoc, hV]; exact ((𝒢 (DualNumber k) Wq hΔq).mul t x y).2⟩ :
          SchemeHomOver t (projModelStrCR W.toProjective)) =
        (𝒢 (DualNumber k) W hΔW).mul t ⟨x.1 ≫ Vq, by rw [Category.assoc, hV]; exact x.2⟩ ⟨y.1 ≫ Vq, by rw [Category.assoc, hV]; exact y.2⟩)
    [IsFinite Vq] [Flat Vq] [LocallyOfFinitePresentation Vq] [Surjective Vq]
    (m : ℕ) (hVrk : ∀ p, Vq.finrank p = m)
    (hVO : (kwZeroSect (DualNumber k) Wq).1 ≫ Vq = (kwZeroSect (DualNumber k) W).1) :
    ∃ g : projModelCR Wq.toProjective ⟶ projModelCR (W₀.map (algebraMap k (DualNumber k))).toProjective,
      ∃ hg : g ≫ projModelStrCR (W₀.map (algebraMap k (DualNumber k))).toProjective = projModelStrCR Wq.toProjective,
      (∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR Wq.toProjective)),
        (⟨((𝒢 (DualNumber k) Wq hΔq).mul t x y).1 ≫ g, by rw [Category.assoc, hg]; exact ((𝒢 (DualNumber k) Wq hΔq).mul t x y).2⟩ :
            SchemeHomOver t (projModelStrCR (W₀.map (algebraMap k (DualNumber k))).toProjective)) =
          (𝒢 (DualNumber k) (W₀.map (algebraMap k (DualNumber k))) hΔ₀).mul t
            ⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩) ∧
      IsFinite g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g ∧
      (∀ p, g.finrank p = m) ∧
      (kwZeroSect (DualNumber k) Wq).1 ≫ g = (kwZeroSect (DualNumber k) (W₀.map (algebraMap k (DualNumber k)))).1 ∧
      (∀ (P : Section Wq.toProjective) (x₀ y₀ : k),
        IsSectionThrough P (algebraMap k (DualNumber k) x₀) (algebraMap k (DualNumber k) y₀) →
        P.1 ≫ Vq = (kwZeroSect (DualNumber k) W).1 →
        P.1 ≫ g = (kwZeroSect (DualNumber k) (W₀.map (algebraMap k (DualNumber k)))).1) ∧
      (∀ (φ : projModelGradingCR W.toProjective →+*ᵍ
            projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective)
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
        (_ : IsCoefficientHom W.toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ)
        (φ' : projModelGradingCR (W₀.map (algebraMap k (DualNumber k))).toProjective →+*ᵍ
            projModelGradingCR (((W₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom)).toProjective)
        (hφ' : HomogeneousIdeal.irrelevant
            (projModelGradingCR (((W₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom)).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR (W₀.map (algebraMap k (DualNumber k))).toProjective)).map φ')
        (_ : IsCoefficientHom (W₀.map (algebraMap k (DualNumber k))).toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ')
        (hW' : ((W₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom) =
          W.map (TrivSqZeroExt.fstHom k k k).toRingHom),
        ∃ (Z : Scheme) (e : Z ⟶ projModelCR Wq.toProjective)
          (v : Z ⟶ projModelCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective),
          Epi v ∧
          e ≫ Vq = v ≫ Proj.map φ hφ ∧
          e ≫ g = v ≫ eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hW')).symm ≫ Proj.map φ' hφ') := by
  classical
  subst hconst hW₀

  have hπι : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp (algebraMap k (DualNumber k)) = RingHom.id k := RingHom.ext fun a => by simp
  have h₁ : (Wq₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom = Wq₀ := by
    rw [WeierstrassCurve.map_map, hπι, WeierstrassCurve.map_id]
  have hιinj : Function.Injective (algebraMap k (DualNumber k)) := fun a b hab => by
    have := congrArg TrivSqZeroExt.fst hab
    first | exact this | simpa [TrivSqZeroExt.algebraMap_eq_inl] using this
  have hΔq₀ : IsUnit Wq₀.Δ := by
    have h := hΔq
    rw [WeierstrassCurve.map_Δ, TrivSqZeroExt.isUnit_iff_isUnit_fst] at h
    first | exact h | simpa [TrivSqZeroExt.algebraMap_eq_inl] using h
  have hΔπ : IsUnit (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).Δ := by rw [WeierstrassCurve.map_Δ]; exact hΔW.map _
  letI : Algebra A k := (((TrivSqZeroExt.fstHom k k k).toRingHom).comp (algebraMap A (DualNumber k))).toAlgebra

  obtain ⟨φ₁, hφ₁, hc₁⟩ := exists_coefHom (TrivSqZeroExt.fstHom k k k).toRingHom (Wq₀.map (algebraMap k (DualNumber k))) Wq₀ h₁
  obtain ⟨φ₂, hφ₂, hc₂⟩ := exists_coefHom (TrivSqZeroExt.fstHom k k k).toRingHom W (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) rfl
  obtain ⟨ψ₁, hψ₁, hd₁⟩ := exists_coefHom (algebraMap k (DualNumber k)) Wq₀ (Wq₀.map (algebraMap k (DualNumber k))) rfl
  obtain ⟨ψ₂, hψ₂, hd₂⟩ := exists_coefHom (algebraMap k (DualNumber k)) (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))) rfl
  have hpbφ₁ := isPullback_gen (TrivSqZeroExt.fstHom k k k).toRingHom (Wq₀.map (algebraMap k (DualNumber k))) Wq₀ h₁ φ₁ hφ₁ hc₁
  have hpbφ₂ := isPullback_gen (TrivSqZeroExt.fstHom k k k).toRingHom W (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) rfl φ₂ hφ₂ hc₂
  have hpbψ₁ := isPullback_gen (algebraMap k (DualNumber k)) Wq₀ (Wq₀.map (algebraMap k (DualNumber k))) rfl ψ₁ hψ₁ hd₁
  have hpbψ₂ := isPullback_gen (algebraMap k (DualNumber k)) (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))) rfl ψ₂ hψ₂ hd₂

  obtain ⟨v, hv, hvsq, hvpb⟩ := exists_baseChange_gen (TrivSqZeroExt.fstHom k k k).toRingHom (Wq₀.map (algebraMap k (DualNumber k))) W Wq₀ (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) h₁ rfl Vq hV φ₁ hφ₁ hc₁ φ₂ hφ₂ hc₂
  obtain ⟨g, hg, hgsq, hgpb⟩ := exists_baseChange_gen (algebraMap k (DualNumber k)) Wq₀ (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) (Wq₀.map (algebraMap k (DualNumber k))) ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))) rfl rfl v hv
    ψ₁ hψ₁ hd₁ ψ₂ hψ₂ hd₂

  have vhom := fun {S : Scheme} (t : S ⟶ Spec (CommRingCat.of k))
      (x y : SchemeHomOver t (projModelStrCR Wq₀.toProjective)) => hom_of_comp_projMap_eq 𝒢 h𝒢 h𝒢O (TrivSqZeroExt.fstHom k k k).toRingHom (Wq₀.map (algebraMap k (DualNumber k))) W hΔq hΔW Wq₀ (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) h₁ rfl hΔq₀ hΔπ
    φ₁ hφ₁ hc₁ φ₂ hφ₂ hc₂ Vq hV hVhom v hv hvsq t x y
  have ghom := fun {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k)))
      (x y : SchemeHomOver t (projModelStrCR (Wq₀.map (algebraMap k (DualNumber k))).toProjective)) => hom_of_comp_projMap_eq 𝒢 h𝒢 h𝒢O (algebraMap k (DualNumber k)) Wq₀ (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) hΔq₀ hΔπ (Wq₀.map (algebraMap k (DualNumber k))) ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))) rfl rfl hΔq hΔ₀
    ψ₁ hψ₁ hd₁ ψ₂ hψ₂ hd₂ v hv vhom g hg hgsq t x y

  obtain ⟨vfin, vflat, vlofp, vsurj, vrk⟩ :=
    isFinite_flat_lofp_surjective_finrank_of_isPullback v _ _ Vq hvpb m hVrk
  haveI := vfin; haveI := vflat; haveI := vlofp; haveI := vsurj
  obtain ⟨gfin, gflat, glofp, gsurj, grk⟩ :=
    isFinite_flat_lofp_surjective_finrank_of_isPullback g _ _ v hgpb m vrk

  have hone_q := (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect (Wq₀.map (algebraMap k (DualNumber k)))
    (𝒢 (DualNumber k) (Wq₀.map (algebraMap k (DualNumber k))) hΔq)).mp (h𝒢O (DualNumber k) (Wq₀.map (algebraMap k (DualNumber k))).toProjective hΔq)
  have hone_t := (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k)))
    (𝒢 (DualNumber k) ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))) hΔ₀)).mp (h𝒢O (DualNumber k) ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))).toProjective hΔ₀)
  refine ⟨g, hg, ghom, gfin, gflat, glofp, gsurj, grk, ?_, ?_, ?_⟩
  ·
    rw [← hone_q, ← hone_t]
    exact one_comp_eq_one _ _ g hg ghom (𝟙 _)
  ·
    intro P x₀ y₀ hP hPV
    have hEq : (Wq₀.map (algebraMap k (DualNumber k))).toAffine.Equation ((algebraMap k (DualNumber k)) x₀) ((algebraMap k (DualNumber k)) y₀) :=
      ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
        (Wq₀.map (algebraMap k (DualNumber k))).toProjective).1 _ _).mpr ⟨P, hP⟩
    have hEq₀ : Wq₀.toAffine.Equation x₀ y₀ := (WeierstrassCurve.Affine.map_equation _ hιinj x₀ y₀).mp hEq
    obtain ⟨P₀, hP₀⟩ := ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
        Wq₀.toProjective).1 x₀ y₀).mp hEq₀
    obtain ⟨χ₀, hχ₀, hχ₀x, hχ₀y⟩ := hP₀
    have hχ₀' : P₀.1 = Spec.map (CommRingCat.ofHom χ₀) ≫ zChartι Wq₀.toProjective := hχ₀
    obtain ⟨ρ, hρ, hρx, hρy⟩ := hP
    have hρ' : P.1 = Spec.map (CommRingCat.ofHom ρ) ≫ zChartι (Wq₀.map (algebraMap k (DualNumber k))).toProjective := hρ

    have wP₀ : (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ P₀.1) ≫ projModelStrCR Wq₀.toProjective =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) := by
      rw [Category.assoc, P₀.2, Category.id_comp, Category.comp_id]
    let P₀' : Section (Wq₀.map (algebraMap k (DualNumber k))).toProjective :=
      ⟨hpbψ₁.lift (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ P₀.1) (𝟙 _) wP₀, hpbψ₁.lift_snd _ _ _⟩
    have hP₀' : P₀'.1 ≫ Proj.map ψ₁ hψ₁ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ P₀.1 := hpbψ₁.lift_fst _ _ _
    obtain ⟨a₁, ha₁, ha₁x, ha₁y⟩ := exists_zChart_gen (algebraMap k (DualNumber k)) Wq₀ (Wq₀.map (algebraMap k (DualNumber k))) rfl ψ₁ hψ₁ hd₁
    have hthr' : IsSectionThrough P₀' ((algebraMap k (DualNumber k)) x₀) ((algebraMap k (DualNumber k)) y₀) := by

      have hrange : Set.range P₀'.1 ⊆ Set.range (zChartι (Wq₀.map (algebraMap k (DualNumber k))).toProjective) := by
        rintro _ ⟨z, rfl⟩
        have hz : (Proj.map ψ₁ hψ₁) (P₀'.1 z) ∈ (zChartι Wq₀.toProjective).opensRange := by
          rw [Scheme.Hom.mem_opensRange]
          refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Spec.map (CommRingCat.ofHom χ₀)) z, ?_⟩
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hP₀', hχ₀', Category.assoc]
        have hz' : P₀'.1 z ∈ (zChartι (Wq₀.map (algebraMap k (DualNumber k))).toProjective).opensRange := by
          have e1 : (zChartι Wq₀.toProjective).opensRange =
              Proj.basicOpen (projModelGradingCR Wq₀.toProjective) (coord Wq₀.toProjective 2) :=
            Proj.opensRange_awayι _ _ _ _
          have e2 : (zChartι (Wq₀.map (algebraMap k (DualNumber k))).toProjective).opensRange =
              Proj.basicOpen (projModelGradingCR (Wq₀.map (algebraMap k (DualNumber k))).toProjective) (coord (Wq₀.map (algebraMap k (DualNumber k))).toProjective 2) :=
            Proj.opensRange_awayι _ _ _ _
          rw [e1] at hz
          have hc : ψ₁ (coord Wq₀.toProjective 2) = coord (Wq₀.map (algebraMap k (DualNumber k))).toProjective 2 := hd₁.2 2
          rw [e2, ← hc, ← Proj.map_preimage_basicOpen ψ₁ hψ₁]
          exact hz
        rw [Scheme.Hom.mem_opensRange] at hz'
        exact hz'
      set l := IsOpenImmersion.lift (zChartι (Wq₀.map (algebraMap k (DualNumber k))).toProjective) P₀'.1 hrange with hl_def
      have hl : l ≫ zChartι (Wq₀.map (algebraMap k (DualNumber k))).toProjective = P₀'.1 := IsOpenImmersion.lift_fac _ _ _
      set χ' : ZChartRing (Wq₀.map (algebraMap k (DualNumber k))).toProjective →+* DualNumber k := (Spec.preimage l).hom with hχ'
      have hSpecχ' : Spec.map (CommRingCat.ofHom χ') = l := by
        rw [hχ', CommRingCat.ofHom_hom, Spec.map_preimage]
      have hcomp : χ'.comp a₁ = ((algebraMap k (DualNumber k))).comp χ₀ := by
        have e1 : Spec.map (CommRingCat.ofHom (χ'.comp a₁)) ≫ zChartι Wq₀.toProjective =
            Spec.map (CommRingCat.ofHom (((algebraMap k (DualNumber k))).comp χ₀)) ≫ zChartι Wq₀.toProjective := by
          rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← ha₁, ← Category.assoc, hSpecχ', hl, hP₀', hχ₀',
            ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (zChartι Wq₀.toProjective)).mp e1))
        simpa only [CommRingCat.hom_ofHom] using e2
      refine ⟨χ', ?_, ?_, ?_⟩
      · show P₀'.1 = Spec.map (CommRingCat.ofHom χ') ≫ zChartι (Wq₀.map (algebraMap k (DualNumber k))).toProjective
        rw [hSpecχ', hl]
      · show χ' (xOverZ (Wq₀.map (algebraMap k (DualNumber k))).toProjective) = (algebraMap k (DualNumber k)) x₀
        rw [← ha₁x, ← RingHom.comp_apply, hcomp, RingHom.comp_apply]
        exact congrArg _ hχ₀x
      · show χ' (yOverZ (Wq₀.map (algebraMap k (DualNumber k))).toProjective) = (algebraMap k (DualNumber k)) y₀
        rw [← ha₁y, ← RingHom.comp_apply, hcomp, RingHom.comp_apply]
        exact congrArg _ hχ₀y
    have hPP₀ : P = P₀' :=
      ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
        (Wq₀.map (algebraMap k (DualNumber k))).toProjective).2 P P₀' _ _ _ _ ⟨ρ, hρ, hρx, hρy⟩ hthr').mpr ⟨rfl, rfl⟩
    have hPψ : P.1 ≫ Proj.map ψ₁ hψ₁ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ P₀.1 := by rw [hPP₀]; exact hP₀'

    obtain ⟨b₁, hb₁, hb₁x, hb₁y⟩ := exists_zChart_gen (TrivSqZeroExt.fstHom k k k).toRingHom (Wq₀.map (algebraMap k (DualNumber k))) Wq₀ h₁ φ₁ hφ₁ hc₁
    have hred : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P.1 = P₀.1 ≫ Proj.map φ₁ hφ₁ := by

      have heq : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp ρ = χ₀.comp b₁ := by
        refine ringHom_zChartRing_ext (Wq₀.map (algebraMap k (DualNumber k))).toProjective _ _ (fun t => ?_) ?_ ?_
        ·
          have hρs := comp_scalar_eq_of_comp_eq (zChartι (Wq₀.map (algebraMap k (DualNumber k))).toProjective) (projModelStrCR (Wq₀.map (algebraMap k (DualNumber k))).toProjective)
            _ (zChartι_comp_projModelStrCR (Wq₀.map (algebraMap k (DualNumber k))).toProjective) ρ (RingHom.id (DualNumber k))
            (by rw [← Category.assoc, ← hρ', P.2, CommRingCat.ofHom_id, Spec.map_id])
          have hχ₀s := comp_scalar_eq_of_comp_eq (zChartι Wq₀.toProjective) (projModelStrCR Wq₀.toProjective)
            _ (zChartι_comp_projModelStrCR Wq₀.toProjective) χ₀ (RingHom.id k)
            (by rw [← Category.assoc, ← hχ₀', P₀.2, CommRingCat.ofHom_id, Spec.map_id])
          have hb₁s := comp_eq_comp_of_square (zChartι (Wq₀.map (algebraMap k (DualNumber k))).toProjective) (zChartι Wq₀.toProjective)
            (Proj.map φ₁ hφ₁) (projModelStrCR (Wq₀.map (algebraMap k (DualNumber k))).toProjective) (projModelStrCR Wq₀.toProjective) (TrivSqZeroExt.fstHom k k k).toRingHom hpbφ₁.w
            b₁ hb₁ _ (zChartι_comp_projModelStrCR (Wq₀.map (algebraMap k (DualNumber k))).toProjective) _ (zChartι_comp_projModelStrCR Wq₀.toProjective)
          have e1 := RingHom.congr_fun hρs t
          have e2 := RingHom.congr_fun hb₁s t
          have e3 := RingHom.congr_fun hχ₀s ((TrivSqZeroExt.fstHom k k k).toRingHom t)
          simp only [RingHom.comp_apply, RingHom.id_apply] at e1 e2 e3 ⊢
          rw [e1, e2, e3]
        · simp only [RingHom.comp_apply]
          rw [hb₁x, show ρ (xOverZ (Wq₀.map (algebraMap k (DualNumber k))).toProjective) = algebraMap k (DualNumber k) x₀ from hρx,
            show χ₀ (xOverZ Wq₀.toProjective) = x₀ from hχ₀x]
          simp
        · simp only [RingHom.comp_apply]
          rw [hb₁y, show ρ (yOverZ (Wq₀.map (algebraMap k (DualNumber k))).toProjective) = algebraMap k (DualNumber k) y₀ from hρy,
            show χ₀ (yOverZ Wq₀.toProjective) = y₀ from hχ₀y]
          simp
      rw [hρ', hχ₀', Category.assoc, hb₁, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, heq]

    have hP₀v : P₀.1 ≫ v = (kwZeroSect k (W.map (TrivSqZeroExt.fstHom k k k).toRingHom)).1 := by
      apply hpbφ₂.hom_ext
      · rw [Category.assoc, hvsq, ← Category.assoc, ← hred, Category.assoc, hPV,
          kwZeroSect_comp_projMap (TrivSqZeroExt.fstHom k k k).toRingHom W (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) rfl φ₂ hφ₂ hc₂]
      · rw [Category.assoc, hv, P₀.2, (kwZeroSect k (W.map (TrivSqZeroExt.fstHom k k k).toRingHom)).2]

    apply hpbψ₂.hom_ext
    · rw [Category.assoc, hgsq, ← Category.assoc, hPψ, Category.assoc, hP₀v,
        kwZeroSect_comp_projMap (algebraMap k (DualNumber k)) (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))) rfl ψ₂ hψ₂ hd₂]
    · rw [Category.assoc, hg, P.2, (kwZeroSect (DualNumber k) ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k)))).2]
  ·
    intro φ hφ hcφ φ' hφ' hcφ' hW'
    refine ⟨_, Proj.map φ₁ hφ₁, v, ?_, ?_, ?_⟩
    · haveI := vfin; haveI := vflat; haveI := vlofp; haveI := vsurj
      infer_instance
    · rw [projMap_eq_of_coefHom (TrivSqZeroExt.fstHom k k k).toRingHom W (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) φ φ₂ hφ hφ₂ hcφ hc₂]
      exact hvsq.symm
    · apply hpbψ₂.hom_ext
      ·
        have hidq : Proj.map φ₁ hφ₁ ≫ Proj.map ψ₁ hψ₁ = 𝟙 _ := by
          have h := eqToHom_comp_projMap_eq_id Wq₀ Wq₀ rfl (φ₁.comp ψ₁)
            (HomogeneousIdeal.irrelevant_le_map_comp hψ₁ hφ₁) (fun a => ?_) (fun i => ?_)
          · rw [eqToHom_refl, Category.id_comp, Proj.map_comp] at h
            exact h
          · show φ₁ (ψ₁ (cls Wq₀.toProjective (MvPolynomial.C a))) = cls Wq₀.toProjective (MvPolynomial.C a)
            rw [hd₁.1 a, hc₁.1 ((algebraMap k (DualNumber k)) a)]
            exact congrArg (fun x => cls Wq₀.toProjective (MvPolynomial.C x)) (RingHom.congr_fun hπι a)
          · show φ₁ (ψ₁ (cls Wq₀.toProjective (MvPolynomial.X i))) = cls Wq₀.toProjective (MvPolynomial.X i)
            rw [hd₁.2 i, hc₁.2 i]
        have hidW : eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hW')).symm ≫
            Proj.map φ' hφ' ≫ Proj.map ψ₂ hψ₂ = 𝟙 _ := by
          have h := eqToHom_comp_projMap_eq_id (W.map (TrivSqZeroExt.fstHom k k k).toRingHom) (((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom) hW' (φ'.comp ψ₂)
            (HomogeneousIdeal.irrelevant_le_map_comp hψ₂ hφ') (fun a => ?_) (fun i => ?_)
          · rw [Proj.map_comp] at h
            exact h
          · show φ' (ψ₂ (cls (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective (MvPolynomial.C a))) = cls (((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective (MvPolynomial.C a)
            rw [hd₂.1 a, hcφ'.1 ((algebraMap k (DualNumber k)) a)]
            exact congrArg (fun x => cls (((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective (MvPolynomial.C x)) (RingHom.congr_fun hπι a)
          · show φ' (ψ₂ (cls (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective (MvPolynomial.X i))) = cls (((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective (MvPolynomial.X i)
            rw [hd₂.2 i, hcφ'.2 i]
        rw [Category.assoc, hgsq, ← Category.assoc, hidq, Category.id_comp, Category.assoc, Category.assoc, hidW,
          Category.comp_id]
      ·
        have hpbφ' := isPullback_gen (TrivSqZeroExt.fstHom k k k).toRingHom
          ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k)))
          (((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom)
          rfl φ' hφ' hcφ'
        have hc : eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hW')).symm ≫
            projModelStrCR (((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k))).map
              (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective =
            projModelStrCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective :=
          eqToHom_comp_projModelStrCR _ _ hW'.symm
        simp only [Category.assoc]
        rw [hg, hpbφ₁.w, hpbφ'.w, reassoc_of% hc, reassoc_of% hv]

end S_WeierstrassCurve_DrinfeldGlobal_exists_hom_isFinite_flat_finrank_eq_of_map_map_eq_dualNumber
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_hom_isFinite_flat_finrank_eq_of_map_map_eq_dualNumber (solution)
